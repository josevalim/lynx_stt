module

public import Erlang.program
public import MapUpdateKeep
public import MapUpdateDelete
public import MapPutGradualKeys

@[expose] public section

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

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-! Monotonicity of the maps of `map_update/5` for `:keep` and `:reject` of a value. -/

theorem old_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {κ : MKey} {o : Option V} (h : Old M₁ κ o) :
    Old M₂ κ o :=
  let ⟨u, hu, e⟩ := h; ⟨u, hM u hu, e⟩

theorem newF_mono {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md : String}
    {O₁ O₂ : Option V → Prop} (hO : ∀ o, O₁ o → O₂ o) {o : Option V} (h : NewF den nt₁ nopt md O₁ o) :
    NewF den nt₂ nopt md O₂ o := by
  unfold NewF at *
  rcases h with ⟨⟨x, hx⟩, h⟩ | ⟨h0, h⟩
  · refine Or.inl ⟨⟨x, hO _ hx⟩, ?_⟩
    rcases h with h | ⟨y, e, hy⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, e, hv y hy⟩
  · refine Or.inr ⟨hO _ h0, ?_⟩
    rcases h with ⟨hf, h | ⟨y, e, hy⟩⟩ | hk
    · exact Or.inl ⟨hf, Or.inl h⟩
    · exact Or.inl ⟨hf, Or.inr ⟨y, e, hv y hy⟩⟩
    · exact Or.inr hk

theorem kindHeld_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {d : String} (h : KindHeld M₁ d) :
    KindHeld M₂ d :=
  ⟨fun e F => let ⟨u, hu, s, ns, hs⟩ := h.1 e F; ⟨u, hM u hu, s, ns, hs⟩,
    fun e => let ⟨u, hu, hk⟩ := h.2 e; ⟨u, hM u hu, hk⟩⟩

theorem kindVal_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {d : String} {x : V} (h : KindVal M₁ d x) :
    KindVal M₂ d x :=
  let ⟨u, k, j, hu, e, hx⟩ := h; ⟨u, k, j, hM u hu, e, hx⟩

theorem newDomS_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x)
    {md d : String} {x : V} (h : NewDomS den M₁ nt₁ md d x) : NewDomS den M₂ nt₂ md d x :=
  ⟨hv x h.1, h.2.imp id (kindHeld_mono hM)⟩

theorem domNES_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x)
    {nopt : Bool} {md d : String} (h : DomNES den M₁ nt₁ nopt md d) : DomNES den M₂ nt₂ nopt md d :=
  h.imp id fun ⟨hf, hn⟩ => ⟨hf.imp id (kindHeld_mono hM), hn.imp id fun ⟨x, hx⟩ => ⟨x, hv x hx⟩⟩

theorem keyNES_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md s : String}
    (h : KeyNES den M₁ S₁ nt₁ nopt md s) : KeyNES den M₂ S₂ nt₂ nopt md s :=
  ⟨fun m => h.1 (hS s m), let ⟨o, ho⟩ := h.2; ⟨o, newF_mono hv (fun _ => old_mono hM) ho⟩⟩

theorem updHasS_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md : String} {Ds₁ Ds₂ : List String}
    (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {A₁ A₂ : Prop → Prop → Prop}
    (hA : ∀ (o₁ n₁ o₂ n₂ : Prop), (o₁ → o₂) → (n₁ → n₂) → A₁ o₁ n₁ → A₂ o₂ n₂)
    (h : UpdHasS den M₁ S₁ nt₁ nopt md Ds₁ A₁) : UpdHasS den M₂ S₂ nt₂ nopt md Ds₂ A₂ := by
  rcases h with ⟨s, hk, h⟩ | ⟨d, md', da, hne, h⟩
  · exact Or.inl ⟨s, keyNES_mono hM hS hv hk, hA _ _ _ _ (fun ⟨x, hx⟩ => ⟨x, old_mono hM hx⟩)
      (fun ⟨x, hx⟩ => ⟨x, newF_mono hv (fun _ => old_mono hM) hx⟩) h⟩
  · exact Or.inr ⟨d, hD d md', da, domNES_mono hM hv hne, hA _ _ _ _ (fun ⟨x, hx⟩ => ⟨x, kindVal_mono hM hx⟩)
      (fun ⟨x, hx⟩ => ⟨x, newDomS_mono hM hv hx⟩) h⟩

/-- Not keeping, with a value: some update gives a value as soon as some update is not empty. -/
theorem upd_present {M : MW V → Prop} {S : List String} {nt : Term} {md : String} {Ds : List String}
    (hmd : md = "force" ∨ md = "reject") (vne : ∃ x, den nt x)
    (h : UpdHasS den M S nt Bool.false md Ds (fun _ _ => True)) :
    UpdHasS den M S nt Bool.false md Ds (fun _ n => n) := by
  obtain ⟨x, hx⟩ := vne
  rcases h with ⟨s, hk, -⟩ | ⟨d, md', da, hne, -⟩
  · refine Or.inl ⟨s, hk, x, ?_⟩
    obtain ⟨o, ho⟩ := hk.2
    unfold NewF at ho ⊢
    rcases ho with ⟨ho, -⟩ | ⟨h0, h⟩
    · exact Or.inl ⟨ho, Or.inr ⟨x, rfl, hx⟩⟩
    · rcases h with ⟨hf, -⟩ | ⟨hk', -⟩
      · exact Or.inr ⟨h0, Or.inl ⟨hf, Or.inr ⟨x, rfl, hx⟩⟩⟩
      · rcases hmd with rfl | rfl <;> simp at hk'
  · refine Or.inr ⟨d, md', da, hne, x, hx, ?_⟩
    rcases hne with hk | ⟨hf, -⟩
    · rcases hmd with rfl | rfl <;> simp at hk
    · exact hf

/-- Keeping a value, no update removes the values of a key or a kind. -/
theorem keep_noLoss {M : MW V → Prop} {S : List String} {nt : Term} {Ds : List String} (vne : ∃ x, den nt x) :
    ¬UpdHasS den M S nt Bool.false "keep" Ds (fun o n => o ∧ ¬n) := by
  obtain ⟨x, hx⟩ := vne
  rintro (⟨s, -, ho, hn⟩ | ⟨d, -, da, -, ⟨y, u, k, j, hu, e, hy⟩, hn⟩)
  · obtain ⟨y, hy⟩ := ho
    exact hn ⟨x, Or.inl ⟨⟨y, hy⟩, Or.inr ⟨x, rfl, hx⟩⟩⟩
  · exact hn ⟨x, hx, Or.inr ⟨fun h => absurd h da, fun _ => ⟨u, hu, k, j, e, by rw [hy]; simp⟩⟩⟩

theorem outV_mono {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {o : Option V} (h : OutV den nt₂ o) :
    OutV den nt₁ o :=
  h.imp id fun ⟨x, e, hx⟩ => ⟨x, e, fun h' => hx (hv x h')⟩

/-- The box is monotone in the type, the atoms of the key type, the kinds and the value. -/
theorem boxSem_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String}
    (hS : ∀ s, s ∈ S₂ → s ∈ S₁) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) (vne : ∃ x, den nt₁ x)
    {md : String} (hmd : Mode md) {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V}
    (h : BoxSem den M₁ S₁ nt₁ Bool.false md Ds₁ w) : BoxSem den M₂ S₂ nt₂ Bool.false md Ds₂ w := by
  obtain ⟨pre₁, hs₁, hn₁⟩ := h
  have pre₂ := updHasS_mono hM hS hv hD (A₁ := fun _ _ => True) (A₂ := fun _ _ => True) (fun _ _ _ _ _ _ h => h) pre₁
  have rs : ∀ s, RS den M₂ S₂ nt₂ Bool.false md Ds₂ s → RS den M₁ S₁ nt₁ Bool.false md Ds₁ s := by
    rintro s ⟨hr, nd, hk, uq⟩
    have nd₁ : ∀ d ∈ Ds₁, d ≠ "atom" → ¬DomNES den M₁ nt₁ Bool.false md d := fun d md' da h' =>
      nd d (hD d md') da (domNES_mono hM hv h')
    rcases pre₁ with ⟨s', hk', -⟩ | ⟨d, md', da, hne, -⟩
    · have := uq s' (keyNES_mono hM hS hv hk')
      subst this
      exact ⟨hr, nd₁, hk', fun s'' h'' => uq s'' (keyNES_mono hM hS hv h'')⟩
    · exact absurd hne (nd₁ d md' da)
  have fullD : (∀ d ∈ domainKinds, d ∈ Ds₁) → ∀ d ∈ domainKinds, d ∈ Ds₂ := fun h d m => hD d (h d m)
  have pres : md ≠ "keep" → PresentS den M₁ S₁ nt₁ Bool.false md Ds₁ := fun nk =>
    ⟨fun hk => absurd hk nk, fun _ => upd_present (by rcases hmd with h | h | h <;> simp_all) vne pre₁⟩
  refine ⟨pre₂, fun hs₂ => ?_, fun ns₂ => ?_⟩
  · have hs₁' : SameS den M₁ S₁ nt₁ Bool.false md Ds₁ := ⟨hs₂.1, fun h' => hs₂.2 (updHasS_mono hM hS hv hD
      (A₁ := fun o n => o ∨ n) (A₂ := fun o n => o ∨ n) (fun _ _ _ _ ho hn h => h.imp ho hn) h')⟩
    exact hM w (hs₁ hs₁')
  by_cases sm₁ : SameS den M₁ S₁ nt₁ Bool.false md Ds₁
  · have wM := hM w (hs₁ sm₁)
    have hk : md = "keep" := sm₁.1
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hk hc.2.1, fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp at this
    · cases e : w (.dom k i) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl, Or.inl ⟨w, k, i, wM, rfl, e⟩⟩
    · rintro rfl; exact (hp.1 hk).2 wM
  obtain ⟨⟨ha, hd⟩, hq⟩ := hn₁ sm₁
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => ?_, fun nc => ?_⟩⟩
  · rcases ha s with ⟨sS1, h⟩ | ⟨nS1, ⟨nr, h⟩ | h⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, old_mono hM h⟩
      · exact Or.inr ⟨sS, Or.inl ⟨fun r => (rs s r).2.2.1.1 sS1, old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inl ⟨fun r => nr (rs s r), old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inr (newF_mono hv (fun _ => old_mono hM) h)⟩
  · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, Or.inl (kindVal_mono hM hx)⟩
    · exact Or.inr ⟨x, h, Or.inr ⟨hD _ dk, newDomS_mono hM hv hx⟩⟩
  · have hc₁ : Bool.false = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds₁ :=
      ⟨rfl, hc.2.1, fun f => hc.2.2 (fullD f)⟩
    intro hu
    exact (hq (pres hc.2.1)).1 hc₁ ⟨fun s nS1 => outV_mono hv (hu.1 s fun m => nS1 (hS s m)),
      fun k i dk => outV_mono hv (hu.2 k i (hD _ dk))⟩
  · by_cases hk : md = "keep"
    · subst hk
      have p₁ : PresentS den M₁ S₁ nt₁ Bool.false "keep" Ds₁ :=
        ⟨fun _ => ⟨keep_noLoss vne, fun h0 => (hp.1 rfl).2 (hM _ h0)⟩, fun h => absurd rfl h⟩
      exact (hq p₁).2 fun c => c.2.1 rfl
    · by_cases c₁ : Bool.false = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds₁
      · rintro rfl
        exact (hq (pres hk)).1 c₁ ⟨fun s _ => Or.inl rfl, fun k i _ => Or.inl rfl⟩
      · exact (hq (pres hk)).2 c₁

theorem keepSemM_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {keep : Bool} {a : String} {w : MW V} (h : KeepSemM den M₁ v₁ keep a w) : KeepSemM den M₂ v₂ keep a w := by
  rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨hk, hn, hw⟩
  · exact Or.inl ⟨⟨x, e, hv x hx⟩, y, hM _ hy⟩
  · exact Or.inr ⟨hk, hn, hM _ hw⟩

theorem agreeP_mono {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {P₁ P₂ : String → V → Prop}
    (hP : ∀ d x, P₁ d x → P₂ d x) {F : List MKey} {w u : MW V} (h : AgreeP Ds₁ P₁ F w u) : AgreeP Ds₂ P₂ F w u := by
  refine ⟨h.1, fun k i nk => h.2.1 k i fun m => nk (hD _ m), fun k i mF dk => ?_⟩
  by_cases d₁ : domKind k ∈ Ds₁
  · rcases h.2.2 k i mF d₁ with e | e | ⟨x, e, hx⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨x, e, hP _ x hx⟩)
  · exact Or.inr (Or.inl (h.2.1 k i d₁))

theorem wres_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {md : String} {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V} (h : WRes den M₁ v₁ md Ds₁ w) :
    WRes den M₂ v₂ md Ds₂ w := by
  obtain ⟨hs, he⟩ := h
  refine ⟨fun F => ?_, fun _ => ⟨fun hk h0 => hM _ ((he vne).1 hk h0), (he vne).2⟩⟩
  obtain ⟨u, hu, hr, a⟩ := hs F
  exact ⟨u, hM u hu, fun r => let ⟨d, md', hk⟩ := hr r; ⟨d, hD d md', hk⟩,
    agreeP_mono hD (fun d x h => ⟨hv x h.1, h.2⟩) a⟩

/-- An update at a named atom of the key type gives maps of the box. -/
theorem keep_box {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {keep : Bool} {S : List String} {Ds : List String} {a : String} (ha : a ∉ S) {w : MW V}
    (h : KeepSemM den M₁ v₁ keep a w) : BoxSem den M₂ S v₂ Bool.false (modeS keep) Ds w := by
  -- The key's old field and its update.
  have keyA : KeyNES den M₂ S v₂ Bool.false (modeS keep) a := by
    refine ⟨ha, ?_⟩
    rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨rfl, hn, hw⟩
    · exact ⟨some x, Or.inl ⟨⟨y, _, hM _ hy, by simp [setK]⟩, Or.inr ⟨x, rfl, hv x hx⟩⟩⟩
    · exact ⟨none, Or.inr ⟨⟨w, hM _ hw, hn⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
  have notR : ∀ s, s ≠ a → ¬RS den M₂ S v₂ Bool.false (modeS keep) Ds s := fun s ne r => ne (r.2.2.2 a keyA).symm
  refine ⟨Or.inl ⟨a, keyA, trivial⟩, fun hs => ?_, fun ns => ?_⟩
  · rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨-, -, hw⟩
    · exact absurd (Or.inl ⟨a, keyA, Or.inl ⟨y, _, hM _ hy, by simp [setK]⟩⟩) hs.2
    · exact hM _ hw
  rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨hk, hn, hw⟩
  · -- The key holds a value of the type.
    have u₀ := hM _ hy
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun _ => ⟨fun _ hu => ?_, fun _ => ?_⟩⟩
    · by_cases sa : s = a
      · subst sa
        refine Or.inr ⟨ha, Or.inr ?_⟩
        rw [e]
        exact Or.inl ⟨⟨y, _, u₀, by simp [setK]⟩, Or.inr ⟨x, rfl, hv x hx⟩⟩
      · have ew : w (.atom s) = setK a (some y) w (.atom s) := by simp [setK, sa]
        by_cases sS : s ∈ S
        · exact Or.inl ⟨sS, _, u₀, ew.symm⟩
        · exact Or.inr ⟨sS, Or.inl ⟨notR s sa, _, u₀, ew.symm⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨_, k, i, u₀, rfl, by simp [setK, e']⟩⟩
    · rcases hu.1 a ha with h' | ⟨z, h', hz⟩
      · rw [e] at h'; cases h'
      · rw [e] at h'; cases h'; exact hz (hv x hx)
    · intro e0; rw [e0] at e; simp [wNone] at e
  · -- Keeping a map lacking the key.
    have wM := hM _ hw
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => ?_, fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp [modeS] at this
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨w, k, i, wM, rfl, e'⟩⟩
    · exact absurd (by rw [hk]; rfl) hc.2.1
    · rintro rfl
      exact (hp.1 (by rw [hk]; rfl)).2 wM

/-- Rejecting with every kind in the box: the widened kinds give maps of the box. -/
theorem widen_box {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {S Ws Ds : List String} (hA : "atom" ∉ Ws) (hD : ∀ d ∈ Ws, d ∈ Ds)
    (hfull : ∀ d ∈ domainKinds, d ∈ Ds) {w : MW V}
    (h : WRes den M₁ v₁ "reject" Ws w) : BoxSem den M₂ S v₂ Bool.false "reject" Ds w := by
  obtain ⟨hs, he⟩ := h
  obtain ⟨u₀, hu₀, hr₀, a₀⟩ := hs []
  obtain ⟨d₀, md₀, hk₀⟩ := hr₀ rfl
  have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
  obtain ⟨x₀, hx₀⟩ := vne
  have dne : DomNES den M₂ v₂ Bool.false "reject" d₀ :=
    Or.inr ⟨Or.inr ⟨fun e => absurd e da, fun _ => ⟨u₀, hM _ hu₀, hk₀⟩⟩, Or.inr ⟨x₀, hv x₀ hx₀⟩⟩
  refine ⟨Or.inr ⟨d₀, hD d₀ md₀, da, dne, trivial⟩, fun hs' => absurd hs'.1 (by simp), fun _ => ?_⟩
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun _ => ⟨fun hc _ => hc.2.2 hfull, fun _ => (he ⟨x₀, hx₀⟩).2 (by simp)⟩⟩
  · by_cases sS : s ∈ S
    · exact Or.inl ⟨sS, u₀, hM _ hu₀, (a₀.1 s).symm⟩
    · exact Or.inr ⟨sS, Or.inl ⟨fun r => r.2.1 d₀ (hD d₀ md₀) da dne, u₀, hM _ hu₀, (a₀.1 s).symm⟩⟩
  · obtain ⟨u, hu, -, a⟩ := hs [.dom k i]
    by_cases dk : domKind k ∈ Ws
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx, hK⟩
      · exact Or.inl e
      · cases e' : u (.dom k i) with
        | none => exact Or.inl (e.trans e')
        | some z => exact Or.inr ⟨z, e.trans e', Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩
      · have hK' : HasKind u (domKind k) := hK.resolve_left (by simp)
        exact Or.inr ⟨x, e, Or.inr ⟨hD _ dk, hv x hx, Or.inr ⟨fun e => absurd e (domKind_ne_atom k), fun _ =>
          ⟨u, hM _ hu, hK'⟩⟩⟩⟩
    · rw [a.2.1 k i dk]
      cases e' : u (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩

/-- `map_update/5` for `:keep` and `:reject` of a value is monotone in the type, the keys and the value. -/
theorem upd_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {keep : Bool} {rs₁ rs₂ Ds₁ Ds₂ Dm₁ Dm₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hDm₁ : ∀ d, d ∈ Dm₁ ↔ d ∈ Ds₁ ∧ (keep = Bool.true ∨ KindHeld M₁ d))
    (hDm₂ : ∀ d, d ∈ Dm₂ ↔ d ∈ Ds₂ ∧ (keep = Bool.true ∨ KindHeld M₂ d)) {w : MW V}
    (h : UpdSemKR den M₁ rs₁ neg₁ Dm₁ v₁ keep w) : UpdSemKR den M₂ rs₂ neg₂ Dm₂ v₂ keep w := by
  classical
  have hD₁ : ∀ s ∈ Ds₁, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok₁.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  -- The kinds of the small split are kinds of the large one.
  have dsub : ∀ d ∈ Ds₁, d ∈ Ds₂ := by
    intro d md
    by_cases da : d = "atom"
    · subst da
      obtain ⟨N₁, e₁⟩ := ok₁.hatom.mp (List.mem_map_of_mem md)
      subst e₁
      obtain ⟨c, hc⟩ := fresh_str (keyStrs N₁ ++ rs₂)
      have k₂ := hK (.atom c) (Or.inr ⟨N₁, rfl, lookup_fresh' fun m => hc (List.mem_append_left _ m)⟩)
      rcases k₂ with m | ⟨N₂, e₂, -⟩
      · obtain ⟨c', mc', e⟩ := List.mem_map.mp m
        cases e; exact absurd (List.mem_append_right _ mc') hc
      · have := ok₂.hatom.mpr ⟨N₂, e₂⟩
        obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    · obtain ⟨k, rfl⟩ := domKind_of (hD₁ _ md) da
      have := hK (.dom k 0) (List.mem_map_of_mem md)
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
  have dmsub : ∀ d ∈ Dm₁, d ∈ Dm₂ := fun d m => by
    obtain ⟨md, h'⟩ := (hDm₁ d).mp m
    exact (hDm₂ d).mpr ⟨dsub d md, h'.imp id (kindHeld_mono hM)⟩
  have fullM : FullK Dm₁ → FullK Dm₂ := fun f d m => dmsub d (f d m)
  have filt : ∀ (p : String → Bool) d, d ∈ Dm₁.filter p → d ∈ Dm₂.filter p := fun p d m => by
    rw [List.mem_filter] at m ⊢; exact ⟨dmsub d m.1, m.2⟩
  have rmode : keep = Bool.false → modeS keep = "reject" := fun e => by subst e; rfl
  -- The atoms of the small split are atoms of the large one.
  have named : ∀ a ∈ rs₁, (neg₂ = .atom "nil" → a ∈ rs₂) ∧ ∀ N₂, neg₂ = .map N₂ → a ∉ setStrs N₂ := by
    intro a ma
    have k₂ := hK (.atom a) (Or.inl (List.mem_map_of_mem ma))
    refine ⟨fun e => ?_, fun N₂ e => ?_⟩
    · rcases k₂ with m | ⟨N, e', -⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp m; cases e; exact ma'
      · rw [e] at e'; cases e'
    · rcases k₂ with m | ⟨N, e', hN⟩
      · rw [nr₂ N₂ e] at m; simp at m
      · rw [e] at e'; cases e'; exact fun m => setStrs_mem.mp m hN
  rcases h with ⟨rfl, hn | ⟨dne, hw⟩⟩ | ⟨N₁, rfl, h⟩
  · -- An atom of the small split.
    obtain ⟨a, ma, ha⟩ := hn
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl ⟨a, (named a ma).1 rfl, keepSemM_mono hM hv ha⟩⟩
    · have hb := fun Ds => keep_box (Ds := Ds) hM hv ((named a ma).2 N₂ rfl) ha
      by_cases f : keep = Bool.false ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, hb Dm₂⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (hb _)⟩⟩
  · -- The widened kinds of the small split.
    have nA : "atom" ∉ Dm₁ := fun m => by
      obtain ⟨N, e⟩ := ok₁.hatom.mp (List.mem_map_of_mem ((hDm₁ _).mp m).1); cases e
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ⟨fun e => dne ?_, wres_mono hM hv vne dmsub hw⟩⟩
      cases Dm₁ with
      | nil => rfl
      | cons d _ => have := dmsub d List.mem_cons_self; rw [e] at this; cases this
    · by_cases f : keep = Bool.false ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        rw [rmode kf] at hw
        refine Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, ?_⟩⟩
        rw [rmode kf]
        exact widen_box hM hv vne nA dmsub full hw
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => dne ?_, wres_mono hM hv vne (fun d m => ?_) hw⟩⟩⟩
        · cases Dm₁ with
          | nil => rfl
          | cons d _ =>
            have := filt (fun x => decide (x ≠ "atom")) d (by
              simp only [List.mem_filter, List.mem_cons_self, true_and, decide_eq_true_eq]
              exact fun e' => nA (e' ▸ List.mem_cons_self))
            rw [e] at this; cases this
        · exact filt (fun x => decide (x ≠ "atom")) d (List.mem_filter.mpr ⟨m, by
            simp only [decide_eq_true_eq]; exact fun e' => nA (e' ▸ m)⟩)
  · -- The box and the widened kinds of a negated set.
    have at₁ : "atom" ∈ Ds₁ := by
      have := ok₁.hatom.mpr ⟨N₁, rfl⟩
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    obtain ⟨N₂, e₂⟩ : ∃ N₂, neg₂ = .map N₂ := ok₂.hatom.mp (List.mem_map_of_mem (dsub _ at₁))
    subst e₂
    have hS : ∀ s, s ∈ setStrs N₂ → s ∈ setStrs N₁ := fun s m => Classical.byContradiction fun nm => by
      have hN₁ : mapLookup N₁ (.atom s) = none := by
        cases e : mapLookup N₁ (.atom s) with
        | none => rfl
        | some _ => exact absurd (setStrs_mem.mpr (by rw [e]; simp)) nm
      have k₂ := hK (.atom s) (Or.inr ⟨N₁, rfl, hN₁⟩)
      rcases k₂ with m' | ⟨N, e, hN⟩
      · rw [nr₂ N₂ rfl] at m'; simp at m'
      · cases e; exact setStrs_mem.mp m hN
    have bm := fun {Ds₁' Ds₂' : List String} (hD : ∀ d ∈ Ds₁', d ∈ Ds₂') {w : MW V}
      (h : BoxSem den M₁ (setStrs N₁) v₁ Bool.false (modeS keep) Ds₁' w) =>
      boxSem_mono hM hS hv vne (mode_modeS keep) hD h
    rcases h with ⟨kf, full, hb⟩ | ⟨nf, hb | ⟨wne, hw⟩⟩
    · exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, fullM full, bm dmsub hb⟩⟩
    · by_cases f : keep = Bool.false ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, bm (fun d m => dmsub d (List.mem_filter.mp m).1) hb⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (bm (filt _) hb)⟩⟩
    · have nA : "atom" ∉ Dm₁.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      by_cases f : keep = Bool.false ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        rw [rmode kf] at hw
        refine Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, ?_⟩⟩
        rw [rmode kf]
        exact widen_box hM hv vne nA (fun d m => dmsub d (List.mem_filter.mp m).1) full hw
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => wne ?_, wres_mono hM hv vne (filt _) hw⟩⟩⟩
        cases h' : Dm₁.filter (· ≠ "atom") with
        | nil => rfl
        | cons d _ =>
          have := filt _ d (by rw [h']; exact List.mem_cons_self)
          rw [e] at this; cases this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Two successful `map_update/5` of static values at static key types, asking for the old values, on static maps of
the next level: a smaller type, smaller keys and a smaller non-empty value give fewer maps. -/
theorem upd_sub {XL XR : List (Term × Term)} (hXL : DE (level t n).E (.map XL)) (hXR : DE (level t n).E (.map XR))
    (maps : ∀ w, MT t n XL w → MT t n XR w) {k₁ k₂ : Term} {rs₁ rs₂ Ds₁ Ds₂ : List String} {neg₁ neg₂ : Term}
    {m : Nat}
    (rk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ =
      .ok (splitT (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)))
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (nr₁ : ∀ N, neg₁ = .map N → rs₁ = [])
    (na₁ : ∀ N, neg₁ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (rk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ =
      .ok (splitT (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)))
    (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)) (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (na₂ : ∀ N, neg₂ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (keys : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    {v₁ v₂ : Term} (hv₁ : (level t n).E v₁) (hv₂ : (level t n).E v₂)
    (sv₁ : v₁ = .atom "term" ∨ ∃ Z, v₁ = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (sv₂ : v₂ = .atom "term" ∨ ∃ Z, v₂ = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (vals : ∀ x, (level t n).den v₁ x → (level t n).den v₂ x) (vne : ∃ x, (level t n).den v₁ x) {mode : Term}
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject") (hm : (level t n).K + 26 ≤ m)
    {T₁ Y₁ e₁ T₂ Y₂ e₂ : Term}
    (run₁ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XL) k₁ v₁ mode (.atom "true") =
      .ok (.tuple #[T₁, Y₁, e₁]))
    (run₂ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XR) k₂ v₂ mode (.atom "true") =
      .ok (.tuple #[T₂, Y₂, e₂])) :
    ∃ YL YR, Y₁ = .map YL ∧ Y₂ = .map YR ∧ DE (level t n).E (.map YL) ∧ DE (level t n).E (.map YR) ∧
      SubN t n (.map YL) (.map YR) := by
  have sv₁' : v₁ = .atom "term" ∨ ∃ Z, v₁ = .map Z := sv₁.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have sv₂' : v₂ = .atom "term" ∨ ∃ Z, v₂ = .map Z := sv₂.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have vne₂ : ∃ x, (level t n).den v₂ x := let ⟨x, hx⟩ := vne; ⟨x, vals x hx⟩
  have nr₁' : ∀ N, neg₁ = .map N → rs₁.map Term.atom = [] := fun N e => by rw [nr₁ N e]; rfl
  have nr₂' : ∀ N, neg₂ = .map N → rs₂.map Term.atom = [] := fun N e => by rw [nr₂ N e]; rfl
  have side_kr : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
      {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
        .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
      (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
      (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
      (vne : ∃ x, (level t n).den v x)
      (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {T Y e : Term}
      (keep : Bool)
      (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k v (modeT keep) (.atom "true") =
        .ok (.tuple #[T, Y, e])),
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) ∧
          ∀ w, MT t n Y' w ↔ UpdSemKR (level t n).den (MT t n X) rs neg Dm v keep w := by
    intro X hX k rs Ds neg rk ok nr na v hv vne sv T Y e keep run
    obtain ⟨r, rr, rfl | ⟨er, rfl⟩ | ⟨T', Y', er, rfl, -, dY, oY, Dm, mDm, sY⟩⟩ :=
      kr_update hX rk ok nr na hv vne sv keep hm
    · rw [run] at rr; cases rr
    · rw [run] at rr; cases rr
    · rw [run] at rr
      obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj rr)
      exact ⟨Y', rfl, dY, oY, Dm, mDm, sY⟩
  rcases hmode with rfl | rfl | rfl
  · -- Forcing: the maps of `map_put/3`.
    have side : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
        {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
          .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
        (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
        (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
        (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {T Y e : Term}
        (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k v (.atom "force") (.atom "true") =
          .ok (.tuple #[T, Y, e])),
        ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
          ∀ w, MT t n Y' w ↔ PutSem (level t n).den (MT t n X) (rs.map Term.atom) neg (Ds.map Term.atom) v w := by
      intro X hX k rs Ds neg rk ok nr na v hv sv T Y e run
      obtain ⟨r₁, r₂, put₁, upd₂, ⟨-, rfl⟩ | ⟨-, ⟨er, rfl⟩, -⟩ | ⟨Y'', T', er, rfl, rfl, -⟩⟩ :=
        update_put_old hX rk ok nr na hv sv hm
      · rw [run] at upd₂; cases upd₂
      · rw [run] at upd₂; cases upd₂
      · rw [run] at upd₂
        obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj upd₂)
        obtain ⟨res, rres, ⟨rfl, -⟩ | ⟨Y', rfl, -, dY, oY, sY⟩⟩ :=
          dput hX rk ok (fun N e => by rw [nr N e]; rfl) na hv sv hm
        · rw [rres] at put₁; cases put₁
        · rw [rres] at put₁
          have := Except.ok.inj put₁
          simp only [Term.tuple.injEq, List.cons.injEq, Array.mk.injEq, true_and, and_true] at this
          exact ⟨Y', this.symm, dY, oY, sY⟩
    obtain ⟨YL, rfl, dL, oL, sL⟩ := side hXL rk₁ ok₁ nr₁ na₁ hv₁ sv₁ run₁
    obtain ⟨YR, rfl, dR, -, sR⟩ := side hXR rk₂ ok₂ nr₂ na₂ hv₂ sv₂ run₂
    refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
    obtain ⟨w, hw⟩ := pt_map q (oL q hq)
    rw [hw] at hq ⊢
    exact (sR w).mpr (put_mono maps vals ok₁ ok₂ nr₂' keys ((sL w).mp hq))
  all_goals
    first
    | rw [show Term.atom "keep" = modeT Bool.true from rfl] at run₁ run₂
    | rw [show Term.atom "reject" = modeT Bool.false from rfl] at run₁ run₂
    obtain ⟨YL, rfl, dL, oL, Dm₁, mDm₁, sL⟩ := side_kr hXL rk₁ ok₁ nr₁ na₁ hv₁ vne sv₁ _ run₁
    obtain ⟨YR, rfl, dR, -, Dm₂, mDm₂, sR⟩ := side_kr hXR rk₂ ok₂ nr₂ na₂ hv₂ vne₂ sv₂ _ run₂
    refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
    obtain ⟨w, hw⟩ := pt_map q (oL q hq)
    rw [hw] at hq ⊢
    exact (sR w).mpr (upd_mono maps vals vne ok₁ ok₂ nr₂ keys mDm₁ mDm₂ ((sL w).mp hq))

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! The named keys of `map_update/5` deleting a key: every pair gets the absent field. -/

/-- The final fold of `map_update_project_pair/5` for a deletion: pairs whose old type has values and optional ones
both give the absent field. -/
theorem del_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a : String)
    (Q' : List Term) (hQ : MQOk E den Q') (kQ : KeepsQ (LitA E a) Q')
    (acc : List Term) (ha : UpdQ E a absF Bool.true acc) :
    ∃ Qf, Erlang.lists.«foldl/3» (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_project_pair/5-fun-0-" 2 #[absF])
        (Term.list acc) (Term.list Q') = .ok (Term.list Qf) ∧ UpdQ E a absF Bool.true Qf ∧
      ∀ u, WithF E den absF Qf u ↔
        WithF E den absF acc u ∨ (∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u := by
  obtain ⟨r, ⟨Qf, rfl, uQ, sA⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_project_pair/5-fun-0-" #[absF]
    (fun pre r => ∃ Qf, r = Term.list Qf ∧ UpdQ E a absF Bool.true Qf ∧
      ∀ u, WithF E den absF Qf u ↔
        WithF E den absF acc u ∨ (∃ x, MInPairs E den pre (some x) u) ∨ MInPairs E den pre none u) Q'
    (fun pre q r mq ⟨Qf, er, uQ, sA⟩ => by
      subst er
      obtain ⟨f, b, rfl, ⟨t, o, rfl, ht⟩, fb, nb⟩ := hQ q mq
      obtain ⟨f', b', e', ob⟩ := kQ _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
      obtain ⟨-, rfl⟩ := e'
      obtain ⟨eb, re, se⟩ := ef.empty1 (m := n) hn ht
      let Q₁ := (if o then [Term.tuple #[absF, b]] else []) ++
        ((if eb then [] else [Term.tuple #[absF, b]]) ++ Qf)
      refine ⟨Term.list Q₁, ⟨Q₁, rfl, fun q' mq' => ?_, fun u => ?_⟩, ?_⟩
      · simp only [Q₁, List.mem_append] at mq'
        rcases mq' with mq' | mq' | mq'
        · cases o
          · simp at mq'
          · simp at mq'; subst mq'; exact ⟨absF, b, rfl, Or.inl rfl, fb, ob⟩
        · cases eb
          · simp at mq'; subst mq'; exact ⟨_, b, rfl, Or.inl rfl, fb, ob⟩
          · simp at mq'
        · exact uQ q' mq'
      · have pinS : ∀ x, MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] (some x) u ↔
            den t x ∧ denMF E den b u = Bool.true := fun x => by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have pinN : MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] none u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : WithF E den absF (if eb then [] else [Term.tuple #[absF, b]]) u ↔
            ∃ x, den t x ∧ denMF E den b u = Bool.true := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]
            obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
              have := se.mpr fun v hv => h ⟨v, hv⟩
              cases this
            exact ⟨fun ⟨_, h⟩ => ⟨x, hx, h⟩, fun ⟨_, _, h⟩ => ⟨trivial, h⟩⟩
          · simp only [↓reduceIte]
            exact ⟨fun h => absurd h withF_nil, fun ⟨x, hx, _⟩ => absurd hx (se.mp rfl x)⟩
        have first : WithF E den absF (if o then [Term.tuple #[absF, b]] else []) u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          cases o
          · simp [withF_nil]
          · simp only [↓reduceIte, withF_single, true_and]
        simp only [Q₁, withF_append, sA, mInPairs_append, pinS, pinN, first, mid]
        constructor
        · rintro (h | ⟨x, h⟩ | h | ⟨x, h⟩ | h)
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl ⟨x, Or.inr h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨x, Or.inl h⟩)
          · exact Or.inr (Or.inr (Or.inl h))
        · rintro (h | ⟨x, h | h⟩ | h | h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, h⟩)))
          · exact Or.inr (Or.inl ⟨x, h⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_project_pair/5-fun-0-/2».pure]
        cases o <;> cases eb <;>
          simp [Elixir.Module.Types.Descr.«-map_update_project_pair/5-fun-0-/3», re, Lynx.Term.isMember, boolAtom, Q₁, absF,
            Term.list])
    (Term.list acc) ⟨acc, rfl, ha, fun u => by simp [MInPairs]⟩
  exact ⟨Qf, run, uQ, sA⟩

/-- `map_update_project_pair/5` for a deletion removes the key from the maps of a pair minus negated pairs whose key
holds a value, and with `keep_absent?`, from those without the key. -/
theorem project_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (P : List Term)
    (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) {t : Term} {o : Bool} {rest : Term} (ht : E t)
    (hr : MField E rest) (orest : OField (LitA E a) rest) (nr : ∃ w, denMF E den rest w = Bool.true) (keep : Bool) :
    ∃ Q, Elixir.Module.Types.Descr.«map_update_project_pair/5» (D (n + 2)) (Term.list P) (.tuple #[t, boolAtom o]) rest
        absF (boolAtom keep) = .ok (Term.list Q) ∧ UpdQ E a absF Bool.true Q ∧
      ∀ u, WithF E den absF Q u ↔
        (∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
        (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  have hA : FieldValue E absF := ⟨.map [], Bool.true, rfl, ef.none⟩
  obtain ⟨b₀, rb₀, sb₀⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) hA
  have b₀f : b₀ = Bool.false := by
    cases b₀
    · rfl
    · exact absurd ((delField_sem ef none).mpr rfl) (sb₀.mp rfl none)
  subst b₀f
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 2) (by omega) ht
  obtain ⟨s₁, rs₁, ss₁⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' (field := .tuple #[t, .atom "false"])
    ⟨t, Bool.false, rfl, ht⟩
  obtain ⟨s₂, rs₂, ss₂⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hA
  -- The shortcuts: the full rest from a present key, and from an absent one.
  let s₁₇ := !e && s₁
  let s₂₇ := keep && o && s₂
  let t₂ := if s₁₇ then Term.map [] else t
  let o₂ := if s₂₇ then Bool.false else (keep && o)
  let pairs₁ := (if s₂₇ then [Term.tuple #[absF, rest]] else []) ++
    (if s₁₇ then [Term.tuple #[absF, rest]] else [])
  have ht₂ : E t₂ := by simp only [t₂]; split; exact ef.none; exact ht
  obtain ⟨fe, rfe, sfe⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (⟨t₂, o₂, rfl, ht₂⟩ : FieldValue E _)
  obtain ⟨Q', rQ', qQ', kQ', fQ', sQ'⟩ := mproject_pairs ef hn P hP' ⟨t₂, o₂, rfl, ht₂⟩ hr nr
  have up₁ : UpdQ E a absF Bool.true pairs₁ := by
    intro q mq
    simp only [pairs₁, List.mem_append] at mq
    rcases mq with mq | mq
    · by_cases h : s₂₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨absF, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [ite_eq_right h] at mq; simp at mq
    · by_cases h : s₁₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨_, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [ite_eq_right h] at mq; simp at mq
  obtain ⟨Qf, rQf, uQf, sAf⟩ := del_fold ef (n := n + 1) (by omega) a Q' qQ' (kQ' _ orest kP) pairs₁ up₁
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  have sem₁ : ∀ u, WithF E den absF pairs₁ u ↔ (s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧
      denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    by_cases h₂ : s₂₇ <;> by_cases h₁ : s₁₇ <;> simp [h₁, h₂, withF_single, withF_nil]
  have f₂ : ∀ y, FieldSem den (.tuple #[t₂, boolAtom o₂]) y ↔
      (∃ x, y = some x ∧ s₁₇ = Bool.false ∧ den t x) ∨ (y = none ∧ o₂ = Bool.true) := fun y => by
    rw [fieldSem_mk]
    by_cases h : s₁₇
    · simp only [t₂, h, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact absurd hx (nonx x)
      · rintro (⟨x, -, e, -⟩ | ⟨rfl, h'⟩)
        · cases e
        · exact Or.inl ⟨rfl, h'⟩
    · simp only [t₂, h, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact Or.inl ⟨x, rfl, by simp, hx⟩
      · rintro (⟨x, rfl, -, hx⟩ | ⟨rfl, h'⟩)
        · exact Or.inr ⟨x, rfl, hx⟩
        · exact Or.inl ⟨rfl, h'⟩
  have short₁ : s₁₇ = Bool.true → ∃ x, den t x ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p (some x) u := fun h => by
    simp only [s₁₇, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨o₀, h₀, out⟩ := ss₁.mp h.2
    obtain ⟨x, rfl, hx⟩ := (putField_sem o₀).mp h₀
    exact ⟨x, hx, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  have short₂ : s₂₇ = Bool.true → keep = Bool.true ∧ o = Bool.true ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p none u := by
    intro h
    simp only [s₂₇, Bool.and_eq_true] at h
    obtain ⟨o₀, h₀, out⟩ := ss₂.mp h.2
    rw [absF, delField_sem ef] at h₀
    subst h₀
    exact ⟨h.1.1, h.1.2, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  have o₂e : o₂ = Bool.true ↔ s₂₇ = Bool.false ∧ keep = Bool.true ∧ o = Bool.true := by
    simp only [o₂]
    by_cases h : s₂₇
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, true_and]; try simpa using h
  -- The semantics, from the shortcuts and the pairs of the rest of the fields.
  have toR : ∀ u, ((s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧ denMF E den rest u = Bool.true) ∨
      (∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u →
      (∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
      (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
    rintro u (⟨h | h, hr⟩ | ⟨x, hx⟩ | hx)
    · obtain ⟨hk, ho, out⟩ := short₂ h
      exact Or.inr ⟨hk, ho, hr, fun p mp => out u p mp⟩
    · obtain ⟨x, hx, out⟩ := short₁ h
      exact Or.inl ⟨x, hx, hr, fun p mp => out u p mp⟩
    · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
      obtain ⟨x', e, -, hx'⟩ | ⟨e, -⟩ := (f₂ _).mp hf
      · obtain rfl : x = x' := Option.some.inj e
        exact Or.inl ⟨x, hx', hr, out⟩
      · cases e
    · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
      obtain ⟨x, e, -⟩ | ⟨-, h⟩ := (f₂ _).mp hf
      · cases e
      · obtain ⟨-, hk, ho⟩ := o₂e.mp h
        exact Or.inr ⟨hk, ho, hr, out⟩
  have ofR : ∀ u, ((∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
      (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u)) →
      ((s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧ denMF E den rest u = Bool.true) ∨
      (fe = Bool.false ∧ ((∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u)) := by
    rintro u (⟨x, hx, hr, out⟩ | ⟨hk, ho, hr, out⟩)
    · by_cases h : s₁₇
      · exact Or.inl ⟨Or.inr h, hr⟩
      · have hf := (f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩)
        refine Or.inr ⟨?_, Or.inl ⟨x, (sQ' _ u).mpr ⟨hf, hr, out⟩⟩⟩
        cases fe
        · rfl
        · exact absurd hf (sfe.mp rfl (some x))
    · by_cases h : s₂₇
      · exact Or.inl ⟨Or.inl h, hr⟩
      · have hf := (f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩)
        refine Or.inr ⟨?_, Or.inr ((sQ' _ u).mpr ⟨hf, hr, out⟩)⟩
        cases fe
        · rfl
        · exact absurd hf (sfe.mp rfl none)
  refine ⟨if fe then pairs₁ else Qf, ?_, ?_, fun u => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_project_pair/5»
    have rs₁ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        (.tuple #[t, .atom "false"]) = .ok (boolAtom s₁) := rs₁
    have rs₂ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        absF = .ok (boolAtom s₂) := rs₂
    simp only [s₁₇, s₂₇, t₂, o₂, pairs₁, absF] at rfe rQ' rQf rs₂ rb₀
    clear ss₁ ss₂ sQ' sAf se sfe sb₀ uQf up₁ qQ' kQ' fQ' hP hP' kP sem₁ f₂ short₁ short₂ o₂e toR ofR
    cases fe <;> cases e <;> cases s₁ <;> cases keep <;> cases o <;> cases s₂ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, boolAtom, s₁₇, s₂₇, pairs₁,
        List.cons_append, Term.list] at rfe rQ' rQf rs₁ rs₂ ⊢ <;>
      simp [rb₀, re, rs₁, rs₂, rfe, rQ', rQf, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, absF] <;>
      (rw [rb₀] at rfe; simp [boolAtom] at rfe)
  · cases fe
    · exact uQf
    · exact up₁
  · cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sAf, sem₁]
      refine ⟨toR u, fun h => ?_⟩
      rcases ofR u h with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · simp only [↓reduceIte]
      rw [sem₁]
      refine ⟨fun h => toR u (Or.inl h), fun h => ?_⟩
      rcases ofR u h with h | ⟨e, -⟩
      · exact h
      · cases e

/-- The operation deleting a key with `:keep` or `:reject`. -/
abbrev delOpK (keep : Bool) : Term := .tuple #[.tuple #[.atom "constant", absF], modeT keep]

/-- One line of the general clause of `map_update_named_key/5` deleting a key: the pairs of the line's maps whose key
holds a value, as maps with the key removed, and with `:keep`, of those without the key. -/
theorem line_pairs_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool) {tag : Term}
    {l : List (Term × Term)} {negs : List Term} (g : TagV E tag) (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term) (Q : List Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      Elixir.Module.Types.Descr.«map_update_prepare_pairs/4» (D (n + 2)) (Term.list P) (fieldAt tag l a)
        (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (delOpK keep) = .ok (Term.list Q) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      UpdQ E a absF Bool.true Q ∧
      ∀ w, WithF E den absF Q (eraseK a w) ↔
        (∃ x, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a (some x) w)) ∨
        (keep = Bool.true ∧ InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a none w)) := by
  obtain ⟨k, P, acc', run, hacc, sacc, hf, hb, rest, hP, sP⟩ := split_line ef hn a g sl lits ne ha
  obtain ⟨w₀, hw₀⟩ := ne
  have nr : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr ((msem_at ef g l a w₀).mp (inMLine_iff.mp hw₀).1).2⟩
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  obtain ⟨t, o, ef', ht⟩ := hf
  obtain ⟨Q, rQ, uQ, sA⟩ := project_del ef hn a P hP ht hb orest nr keep
  have line : ∀ w o', InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a o' w) ↔
      FieldSem den (.tuple #[t, boolAtom o]) o' ∧
        denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) = Bool.true ∧
        ∀ p ∈ P, ¬MPairIn E den p o' (eraseK a w) := by
    intro w o'
    rw [inMLine_iff, msem_at ef g l a, ← ef', rest, eraseK_setK, and_assoc]
    simp only [setK, ite_true]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h p mp hp => ?_, fun h N mN hN => ?_⟩)
    · obtain ⟨N, mN, hN⟩ := (sP (setK a o' w)).mpr ⟨p, mp, by simpa [setK, eraseK_setK] using hp⟩
      exact h N mN (by simpa [setK] using hN)
    · obtain ⟨p, mp, hp⟩ := (sP (setK a o' w)).mp (by simpa [setK] using ⟨N, mN, hN⟩)
      exact h p mp (by simpa [setK, eraseK_setK] using hp)
  refine ⟨k, P, acc', Q, run, ?_, hacc, sacc, uQ, fun w => ?_⟩
  · rw [ef']
    cases keep
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom, absF] using rQ
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom, absF] using rQ
  · rw [sA]
    refine or_congr ⟨fun ⟨x, hx, hr, out⟩ => ⟨x, (line w (some x)).mpr ⟨?_, hr, out⟩⟩, fun ⟨x, hx⟩ => ?_⟩ ?_
    · rw [fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩
    · obtain ⟨hf', hr, out⟩ := (line w (some x)).mp hx
      rw [fieldSem_mk] at hf'
      rcases hf' with ⟨h, -⟩ | ⟨x', e, hx'⟩
      · cases h
      · cases e; exact ⟨x, hx', hr, out⟩
    · rw [line, fieldSem_mk]
      constructor
      · rintro ⟨hk, ho, hr, out⟩; exact ⟨hk, Or.inl ⟨rfl, ho⟩, hr, out⟩
      · rintro ⟨hk, ⟨-, ho⟩ | ⟨x, e, -⟩, hr, out⟩
        · exact ⟨hk, ho, hr, out⟩
        · cases e

/-- The line fold of the general clause of `map_update_named_key/5` deleting a key. -/
theorem del_fold_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ (pr : List Term) (F : Term), Erlang.lists.«foldl/3» (D (n + 3))
        (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-0-" 2 #[.atom a, delOpK keep])
        (.tuple #[.nil, .tuple #[.map [], .atom "false"]]) (Term.list lines) = .ok (.tuple #[Term.list pr, F]) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      UpdQ E a absF Bool.true pr ∧
      ∀ w, WithF E den absF pr (eraseK a w) ↔
        (∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) := by
  obtain ⟨r, ⟨pr, F, rfl, hF, sF, uQ, sA⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-0-" #[.atom a, delOpK keep]
    (fun pre r => ∃ (pr : List Term) (F : Term), r = .tuple #[Term.list pr, F] ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ pre, LongM den L a o) ∧
      UpdQ E a absF Bool.true pr ∧
      ∀ w, WithF E den absF pr (eraseK a w) ↔
        (∃ L ∈ pre, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ pre, InMLine den L (setK a none w))) lines
    (fun pre L r mL ⟨pr, F, er, hF, sF, uQ, sA⟩ => by
      subst er
      obtain ⟨⟨tag, l, negs, rfl, g, sl, lits⟩, ne⟩ := hl L mL
      obtain ⟨k, P, acc', Q, rs, rp, hacc, sacc, uQ', sA'⟩ := line_pairs_del ef hn a keep g sl lits ne hF
      refine ⟨_, ⟨Q.reverse ++ pr, acc', rfl, hacc, fun o => ?_, fun q mq => ?_, fun w => ?_⟩, ?_⟩
      · rw [sacc, sF]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨L', mL', h⟩ | h)
          · exact ⟨L', Or.inl mL', h⟩
          · exact ⟨_, Or.inr rfl, h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inl ⟨L', mL', h⟩
          · exact Or.inr h
      · rcases List.mem_append.mp mq with mq | mq
        · exact uQ' q (List.mem_reverse.mp mq)
        · exact uQ q mq
      · have : WithF E den absF (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den absF Q (eraseK a w) ∨ WithF E den absF pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sA', sA]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ((⟨x, h⟩ | ⟨hk, h⟩) | (⟨L', mL', h⟩ | ⟨hk, L', mL', h⟩))
          · exact Or.inl ⟨_, Or.inr rfl, x, h⟩
          · exact Or.inr ⟨hk, _, Or.inr rfl, h⟩
          · exact Or.inl ⟨L', Or.inl mL', h⟩
          · exact Or.inr ⟨hk, L', Or.inl mL', h⟩
        · rintro (⟨L', mL' | rfl, h⟩ | ⟨hk, L', mL' | rfl, h⟩)
          · exact Or.inr (Or.inl ⟨L', mL', h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr ⟨hk, L', mL', h⟩)
          · exact Or.inl (Or.inr ⟨hk, h⟩)
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-0-/4», rs, rp, USort.rev2])
    (.tuple #[.nil, .tuple #[.map [], .atom "false"]])
    ⟨[], _, rfl, (none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o], by simp [UpdQ],
      fun w => by simp [withF_nil]⟩
  exact ⟨pr, F, run, hF, sF, uQ, sA⟩

theorem putAt_none (ef : EF nd E V den tl K) {a : String} {w : MW V} : ¬PutAt den (.map []) a w :=
  fun ⟨x, _, hx⟩ => ef.den_none x hx

/-- The end of the general clause of `map_update_named_key/5` deleting a key: the single group of rests gets the
absent field. -/
theorem del_tail (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) (keep : Bool)
    (pairs : List Term) (hp : UpdQ E a absF Bool.true pairs) :
    ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (m + 1)) (Term.list pairs)
          (delOpK keep)
        let groups ← Erlang.lists.«foldl/3» (D (m + 1))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w) := by
  have hp' : UpdQ E a (.tuple #[.map [], .atom "false"]) Bool.true pairs := fun q mq => by
    obtain ⟨f, b, rfl, hf, fb, ob⟩ := hp q mq
    exact ⟨f, b, rfl, Or.inr ⟨rfl, hf.elim id (·.2)⟩, fb, ob⟩
  have hk : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey (.map []) f := fun q mq => by
    obtain ⟨f, b, rfl, hf, -⟩ := hp' q mq
    exact ⟨f, b, rfl, hf.elim Or.inl fun h => Or.inr h.2⟩
  obtain ⟨entries, rg, inv⟩ := group_fold (m + 1) pairs hk
  obtain ⟨bdds, rb, fb, sb⟩ := group_bdds ef hm a ef.none pairs hp' entries inv
  refine ⟨bdds, fun κ => ?_, fb, fun w => (sb w).trans ⟨fun h => h.elim (fun h' => absurd h'.1 (putAt_none ef)) id,
    Or.inr⟩⟩
  simp [Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2», rg, Erlang.maps.«to_list/1», rb]

/-- The general clause of `map_update_named_key/5` deleting a key, for `:keep` and `:reject`: the maps of the lines
whose key holds a value, without the key, and with `:keep`, those without the key. -/
theorem del_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ow : Term) :
    ∃ (bdds : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (delOpK keep) (.atom "true") ow = .ok (.tuple #[Term.list bdds, F]) ∧ (∀ b ∈ bdds, MField E b) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ ((∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
          (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L w)) := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5»
  split
  · rename_i h; simp at h
  · rename_i h _; cases keep <;> simp [modeT, absF] at h
  rotate_left
  · rename_i h₁ h₂ _; exact absurd rfl h₂
  -- Both paths give the pairs of the lines and their old field.
  have tail : ∀ (pairs : List Term) (F : Term), UpdQ E a absF Bool.true pairs →
      FieldValue E F → (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) →
      (∀ w, WithF E den absF pairs (eraseK a w) ↔ (∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w))) →
      ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (n + 3)) (Term.list pairs)
          (delOpK keep)
        let groups ← Erlang.lists.«foldl/3» (D (n + 3))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (n + 3)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ ((∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
          (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L w)) := by
    intro pairs F hp hF sF sA
    obtain ⟨bdds, rb, fb, sb⟩ := del_tail ef (m := n + 2) (by omega) a keep pairs hp
    refine ⟨bdds, rb, fb, fun w => (sb w).trans ?_⟩
    rw [sA]
    refine ⟨fun ⟨hn, h⟩ => ⟨hn, ?_⟩, fun ⟨hn, h⟩ => ⟨hn, ?_⟩⟩
    all_goals
      have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      first | (rw [e] at h; exact h) | (rw [e]; exact h)
  split
  · rename_i _ _ f heq
    -- One open line without negations: the shortcut.
    obtain ⟨L, rest, rfl⟩ : ∃ L rest, lines = L :: rest := by
      cases lines with
      | nil => simp [Term.list] at heq
      | cons L rest => exact ⟨L, rest, rfl⟩
    simp only [Term.list, Term.cons.injEq] at heq
    obtain ⟨rfl, hr⟩ := heq
    obtain rfl : rest = [] := by cases rest <;> simp_all [Term.list]
    obtain ⟨⟨tag, l, negs, eL, g, sl, lits⟩, ne⟩ := hl _ List.mem_cons_self
    obtain ⟨rfl, rfl, en⟩ := tuple3_inj eL
    obtain rfl : negs = [] := by
      cases negs with
      | nil => rfl
      | cons x xs => simp [Term.list] at en
    have ne : ∃ w, InMLine den (.tuple #[.atom "open", fieldsTerm l, Term.list []]) w := ne
    obtain ⟨k, rpop, -, rest', -⟩ := pop_pair (den := den) ef g sl a
    obtain ⟨k', P, acc', Q, rs, rp, -, -, uQ, sA⟩ := line_pairs_del ef (n := n + 1) (by omega) a keep g sl
      (by simp) ne (none_field ef).1
    have hP : k' = k ∧ P = [] := by
      simp only [Elixir.Module.Types.Descr.«map_split_key_line/5», rpop, Lynx.Except.ok_bind] at rs
      cases hfo : Elixir.Module.Types.Descr.«field_opt_union/3» (D (n + 1 + 2)) (fieldAt (.atom "open") l a)
          (.tuple #[.map [], .atom "false"]) (.map []) with
      | error err => rw [hfo] at rs; cases rs
      | ok c =>
        rw [hfo] at rs
        simp only [Lynx.Except.ok_bind, pure, Except.pure, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq,
          List.cons.injEq, and_true] at rs
        obtain ⟨-, -, e₁, e₂⟩ := rs
        refine ⟨by simpa using e₁.symm, ?_⟩
        cases P with
        | nil => rfl
        | cons x xs => simp [Term.list] at e₂
    obtain ⟨rfl, rfl⟩ := hP
    obtain ⟨w₀, hw₀⟩ := ne
    have h₀ := (inMLine_iff (negs := []) .. |>.mp hw₀).1
    obtain ⟨bdds, rb, fb, sb⟩ := tail Q (fieldAt (.atom "open") l a) uQ (fieldAt_ok ef g sl a)
      (fun o => by
        rw [lit_values ef g a h₀ o]
        simp only [List.mem_singleton, exists_eq_left, LongM]
        exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩)
      (fun w => by simpa using sA w)
    refine ⟨bdds, _, ?_, fb, fieldAt_ok ef g sl a, fun o => ?_, sb⟩
    · simp only [rpop, rp, Lynx.Except.ok_bind]
      exact rb fun b => pure (.tuple #[b, fieldAt (.atom "open") l a])
    · rw [lit_values ef g a h₀ o]
      simp only [List.mem_singleton, exists_eq_left, LongM]
      exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
        fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩
  · -- Otherwise, the fold over the lines.
    obtain ⟨pr, F, runF, hF, sF, uQ, sA⟩ := del_fold_lines ef hn a keep lines hl
    have revW : ∀ f u, WithF E den f pr.reverse u ↔ WithF E den f pr u := fun f u => by
      simp [WithF]
    obtain ⟨bdds, rb, fb, sb⟩ := tail pr.reverse F (fun q mq => uQ q (List.mem_reverse.mp mq)) hF sF
      (fun w => (revW _ _).trans (sA w))
    refine ⟨bdds, F, ?_, fb, hF, sF, sb⟩
    simp only [pure_bind, runF, reverse1_list, Lynx.Except.ok_bind]
    exact rb fun b => pure (.tuple #[b, F])

/-- The maps of a deletion at a key, from the maps of a type: those whose key held a value, without the key, and
unless rejecting, those without the key. -/
def DelAt (M : MW V → Prop) (md : String) (a : String) (w : MW V) : Prop :=
  w (.atom a) = none ∧ ((∃ x, M (setK a (some x) w)) ∨ (md ≠ "reject" ∧ M w))

theorem setK_none_self {a : String} {w : MW V} (hn : w (.atom a) = none) : setK a none w = w := by
  funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]

/-- `map_update_named_key/5` deleting a key, asking for the old field: the maps `DelAt` gives, when building. -/
theorem del_key_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {md : String} (hmd : Mode md) (a : String) (bd : Bool) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (cOp (.map []) Bool.true md) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧
      FieldValue E F ∧ (bd = Bool.false → ba = []) ∧
      (bd = Bool.true → (∀ b ∈ ba, MField E b) ∧
        ∀ w, (∃ b ∈ ba, denMF E den b w = Bool.true) ↔ DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  obtain ⟨F, rF, hF, -⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, fun _ => rfl, fun h => (by cases h)⟩
  rcases hmd with rfl | rfl | rfl
  · obtain ⟨ba, rba, fba, sba⟩ := put_lines ef hn a (leafPut_del ef a) lines hl
    refine ⟨ba, F, by simpa [boolAtom, cOp] using rba Bool.true F fun _ => rF, hF, fun h => (by cases h), fun _ =>
      ⟨fba, fun w => (sba w).trans ⟨fun ⟨hn, L, mL, o, hL⟩ => ⟨hn, ?_⟩, fun ⟨hn, h⟩ => ⟨hn, ?_⟩⟩⟩⟩
    · cases o with
      | none => rw [setK_none_self hn] at hL; exact Or.inr ⟨by simp, L, mL, hL⟩
      | some x => exact Or.inl ⟨x, L, mL, hL⟩
    · rcases h with ⟨x, L, mL, hL⟩ | ⟨-, L, mL, hL⟩
      · exact ⟨L, mL, some x, hL⟩
      · exact ⟨L, mL, none, by rw [setK_none_self hn]; exact hL⟩
  · rw [show cOp (.map []) Bool.true "keep" = delOpK Bool.true from rfl]
    obtain ⟨ba, F', rb, fba, hF', -, sba⟩ := del_lines ef hn a Bool.true lines hl (.atom "true")
    refine ⟨ba, F', by simpa [boolAtom] using rb, hF', fun h => (by cases h), fun _ => ⟨fba, fun w => (sba w).trans ?_⟩⟩
    unfold DelAt
    constructor
    · rintro ⟨hn, ⟨L, mL, x, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨x, L, mL, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | (cases hk; done) | simp), L, mL, h⟩⟩
    · rintro ⟨hn, ⟨x, L, mL, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨L, mL, x, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | rfl | exact absurd rfl hk), L, mL, h⟩⟩
  · rw [show cOp (.map []) Bool.true "reject" = delOpK Bool.false from rfl]
    obtain ⟨ba, F', rb, fba, hF', -, sba⟩ := del_lines ef hn a Bool.false lines hl (.atom "true")
    refine ⟨ba, F', by simpa [boolAtom] using rb, hF', fun h => (by cases h), fun _ => ⟨fba, fun w => (sba w).trans ?_⟩⟩
    unfold DelAt
    constructor
    · rintro ⟨hn, ⟨L, mL, x, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨x, L, mL, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | (cases hk; done) | simp), L, mL, h⟩⟩
    · rintro ⟨hn, ⟨x, L, mL, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨L, mL, x, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | rfl | exact absurd rfl hk), L, mL, h⟩⟩

/-- `map_update_named_keys/8` deleting the keys, asking for the old values, on a static type: the maps `DelAt` gives at
the keys, when building. -/
theorem named_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (req bd : Bool) (st : Bool) :
    ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, Term.list B, Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (cOp (.map []) Bool.true md) (boolAtom req) (boolAtom st)
          (.atom "true") (boolAtom bd) = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  have loop : ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp (.map []) Bool.true md, boolAtom req, boolAtom st, boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))])
          (.tuple #[T, Term.list B, Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
    intro ks
    induction ks with
    | nil =>
      intro B f T Er hT
      exact ⟨B, f, T, Er, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, fun _ => rfl,
        fun _ fB => ⟨fB, fun w => by simp⟩⟩
    | cons a rest ih =>
      intro B f T Er hT
      obtain ⟨ba, F, rb, hF, bF, bT⟩ := del_key_sem ef (n := n) hn lines hl hmd a bd
      obtain ⟨t, o, rfl, ht⟩ := hF
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      -- One step of the fold: the maps of the key are added, and the old values stay a type.
      obtain ⟨f₁, T₁, Er₁, step, hT₁⟩ : ∃ (f₁ : Bool) (T₁ Er₁ : Term),
          (D (n + 4)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp (.map []) Bool.true md, boolAtom req, boolAtom st, boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))]) #[.atom a, .tuple #[T, Term.list B, Er, boolAtom f]] =
            .ok (.tuple #[T₁, Term.list (ba ++ B), Er₁, boolAtom f₁]) ∧ E T₁ := by
        have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
            (cOp (.map []) Bool.true md) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) := rb
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb']
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
      obtain ⟨B', f', T', Er', r₁, hT', bF', bT'⟩ := ih (ba ++ B) f₁ T₁ Er₁ hT₁
      refine ⟨B', f', T', Er', ?_, hT', fun hb => ?_, fun hb fB => ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        simp at step
        simp [step, r₁]
      · rw [bF' hb, bF hb]; rfl
      · obtain ⟨fba, sba⟩ := bT hb
        obtain ⟨fB', sB'⟩ := bT' hb fun b mb => by
          rcases List.mem_append.mp mb with mb | mb
          · exact fba b mb
          · exact fB b mb
        refine ⟨fB', fun w => ?_⟩
        rw [sB']
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (⟨b, mb | mb, hb'⟩ | ⟨a', ma, h⟩)
          · exact Or.inr ⟨a, Or.inl rfl, (sba w).mp ⟨b, mb, hb'⟩⟩
          · exact Or.inl ⟨b, mb, hb'⟩
          · exact Or.inr ⟨a', Or.inr ma, h⟩
        · rintro (⟨b, mb, hb'⟩ | ⟨a', rfl | ma, h⟩)
          · exact Or.inl ⟨b, Or.inr mb, hb'⟩
          · obtain ⟨b, mb, hb'⟩ := (sba w).mpr h; exact Or.inl ⟨b, Or.inl mb, hb'⟩
          · exact Or.inr ⟨a', ma, h⟩
  intro ks B f T Er hT
  obtain ⟨B', f', T', Er', r₁, hT', bF', bT'⟩ := loop ks B f T Er hT
  refine ⟨B', f', T', Er', ?_, hT', bF', bT'⟩
  rcases hmd with rfl | rfl | rfl
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, boolAtom]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      simpa [boolAtom] using r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa [boolAtom] using r₁

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The maps of `map_update_static_dnf/6` deleting a key, from the maps of a type: the deletions at the atoms of the
split, or the box and the widened kinds, at the kinds `Dm` updated. -/
def UpdSemD (den : Term → V → Prop) (M : MW V → Prop) (rs : List String) (neg : Term) (Dm : List String) (md : String)
    (w : MW V) : Prop :=
  (neg = .atom "nil" ∧ ((∃ a ∈ rs, DelAt M md a w) ∨ (Dm ≠ [] ∧ WRes den M (.map []) md Dm w))) ∨
  ∃ N, neg = .map N ∧
    ((md ≠ "keep" ∧ FullK Dm ∧ BoxSem den M (setStrs N) (.map []) Bool.true md Dm w) ∨
     (¬(md ≠ "keep" ∧ FullK Dm) ∧
       (BoxSem den M (setStrs N) (.map []) Bool.true md (Dm.filter (· = "atom")) w ∨
        (Dm.filter (· ≠ "atom") ≠ [] ∧ WRes den M (.map []) md (Dm.filter (· ≠ "atom")) w))))

/-- The named keys of `map_update_static_dnf/6` deleting a key, asking for the old values: the required atoms are
deleted, and no optional ones. -/
theorem named_tail_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (A : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term} (hT₁ : E T₁)
    (errs : Term) (bd : Term) (hbd : bd = .atom "true" ∨ bd = .atom "false") :
    ∃ (T' Er' : Term) (f' : Bool) (B' : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st)
        (.atom "true") (.atom "true") = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T', Term.list B', Er', boolAtom f'])
        (Term.list lines) .nil (cOp (.map []) Bool.true md) (.atom "false") (boolAtom st) (.atom "true") bd =
        .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ (∀ b ∈ B', MField E b) ∧
      ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w := by
  obtain ⟨B', f', T', Er', e0, -, -, bT'⟩ := named_del (st := st) ef (n := n + 2) (by omega) hmd lines hl Bool.true Bool.true
    A Bl fl T₁ errs hT₁
  obtain ⟨fB', sB'⟩ := bT' rfl fBl
  refine ⟨T', Er', f', B', by simpa using e0, ?_, fB', sB'⟩
  rcases hbd with rfl | rfl <;> rcases hmd with rfl | rfl | rfl <;> cases st <;>
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse]

/-- The named keys of `map_update_static_dnf/6` deleting a key at the atoms outside a negated set, asking for the old
values: nothing is built. -/
theorem named_tail_neg_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, errs, boolAtom fl])
        (Term.list lines) (Term.list []) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "false") (boolAtom st)
        (.atom "true") (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ ∃ b ∈ Bl, denMF E den b w = Bool.true := by
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, bT₂⟩ := named_del (st := st) ef (n := n + 2) (by omega) hmd lines hl Bool.true Bool.true
    [] Bl fl T₁ errs hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, bF', -⟩ := named_del (st := st) ef (n := n + 2) (by omega) hmd lines hl Bool.false Bool.false
    ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  exact ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => by rw [sB₂]; simp⟩

/-- `map_update_static_dnf/6` deleting a key at a finite set of atoms and some kinds, asking for the old values. -/
theorem upd_dnf_nil_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (_hne : lines ≠ []) (A : List String)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hna : "atom" ∉ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true")
        (boolAtom st) = .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Dm md) := by
  classical
  have hmd₀ := hmd
  have m₂ : Erlang.erlang.«++/2» (Term.list (A.map Term.atom)) .nil = .ok (Term.list (A.map Term.atom)) := by
    simpa using append_list (A.map Term.atom) []
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have mm : Erlang.erlang.«--/2» .nil (Term.list (A.map Term.atom)) = .ok .nil := by
    simp [Erlang.erlang.«--/2», Term.properList?, e00, Term.list]
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ [])
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, .nil, Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», m₂, Lynx.Except.ok_bind]
    simpa using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, .nil, Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, .nil, Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  by_cases hrej : md = "reject"
  · subst hrej
    simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1»,
      mv, r₁', r₂', rE', Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2»,
      Term.properList?, e00, a0]
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ ("reject" ≠ "reject" ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, Or.inr ((kind_held_ne ef hl (hDs d ms) (fun e => hna (e ▸ ms))).mpr h)⟩
      · rintro ⟨ms, (h | h)⟩
        · exact absurd rfl h
        · exact ⟨d, ms, rfl, (kind_held_ne ef hl (hDs d ms) (fun e => hna (e ▸ ms))).mp h⟩
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self]
      obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp) f₁
        hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
      have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
          ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) ↔
          UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") [] "reject" w := by
        intro w; simp [UpdSemD]
      obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
      simp only [Term.list] at rN1
      rcases hr with ⟨rfl, emp⟩ | ⟨bot, fr, sr⟩
      · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp⟩⟩
        cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inr ⟨r, rfl, fr, sr⟩⟩
        cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr] <;> split <;> simp_all
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      obtain ⟨d0, md0⟩ := List.exists_mem_of_ne_nil val₁ v0
      obtain ⟨s0, -, rfl⟩ := hA1 d0 md0
      have KsNe : Ks ≠ [] := fun e => by have := (mKs s0).mpr md0; rw [e] at this; cases this
      have hA' : "atom" ∉ Ks := fun m => hna ((memKs _).mp m).1
      obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) ef.none Bool.true hmd Ks hA' subKs lines hl'
      have sW := wlg_sem ef hl' (nt := .map []) Bool.true (Or.inl rfl) hmd hA' subKs KsNe
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, rW]
      have memKs' : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
        simpa using memKs d
      rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, neR, lc, fc, sc⟩
      · simp only [↓reduceIte]
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp)
          Bool.true hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) ↔
            UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "reject" w := by
          intro w
          simp only [UpdSemD, List.not_mem_nil, false_and, exists_false, false_or, true_and, reduceCtorEq,
            or_false, ← sW]
          exact ⟨Or.inl, fun h => h.elim id fun ⟨_, h'⟩ => absurd h' (emp w)⟩
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
      · simp only [neR, ↓reduceIte, getMapKeys_single, lc, Option.toList]
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [c]
          (by simpa using fc) Bool.true hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ [c], denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) ↔
            UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "reject" w := by
          intro w
          simp only [UpdSemD, List.mem_singleton, exists_eq_left, sc, sW, reduceCtorEq, false_and, exists_false,
            or_false, true_and, KsNe, ne_eq, not_false_eq_true]
          exact or_comm
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [Term.list] at rN1; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [Term.list] at rN1; simp [rN1, rN2, rr]
  · have hacc : md = "force" ∨ md = "keep" := by rcases hmd with h | h | h <;> simp_all
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs' : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa [hrej] using memKs d
    rcases hacc with rfl | rfl
    · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
        r₁', r₂', rE', Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2»,
        Term.properList?, e00, a0, Lynx.Except.andAlso]
      by_cases d0 : Ds = []
      · subst d0
        have Ks0 : Ks = [] := by
          cases Ks with
          | nil => rfl
          | cons k _ => exact absurd ((memKs k).mp List.mem_cons_self) (by simp)
        subst Ks0
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp) f₁
          hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) ↔
            UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") [] "force" w := by
          intro w; simp [UpdSemD]
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp, Or.inl ⟨rfl, emp⟩⟩
          cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
      · have KsNe : Ks ≠ [] := fun e => by
          obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil Ds d0
          have := (memKs d).mpr md; rw [e] at this; cases this
        have hA' : "atom" ∉ Ks := fun m => hna ((memKs _).mp m)
        obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) ef.none Bool.true hmd Ks hA' subKs lines hl'
        have sW := wlg_sem ef hl' (nt := .map []) Bool.true (Or.inl rfl) hmd hA' subKs KsNe
        have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
          cases Ds with
          | nil => exact absurd rfl d0
          | cons _ _ => simp [Term.list]
        rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, neR, lc, fc, sc⟩
        · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp)
            Bool.true hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
          have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) ↔
              UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "force" w := by
            intro w
            simp only [UpdSemD, List.not_mem_nil, false_and, exists_false, false_or, true_and, reduceCtorEq,
              or_false, ← sW]
            exact ⟨Or.inl, fun h => h.elim id fun ⟨_, h'⟩ => absurd h' (emp w)⟩
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW] at rN1 rN2 ⊢ <;>
              simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW] at rN1 rN2 ⊢ <;>
              simp [rN1, rN2, rr]
        · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [c]
            (by simpa using fc) Bool.true hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
          have sem : ∀ w, ((∃ b ∈ [c], denMF E den b w = Bool.true) ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) ↔
              UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "force" w := by
            intro w
            simp only [UpdSemD, List.mem_singleton, exists_eq_left, sc, sW, reduceCtorEq, false_and, exists_false,
              or_false, true_and, KsNe, ne_eq, not_false_eq_true]
            exact or_comm
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
              getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
              getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]

    · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, m₃,
        r₁', r₂', rE', Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2»,
        Term.properList?, e00, a0, Lynx.Except.andAlso]
      by_cases d0 : Ds = []
      · subst d0
        have Ks0 : Ks = [] := by
          cases Ks with
          | nil => rfl
          | cons k _ => exact absurd ((memKs k).mp List.mem_cons_self) (by simp)
        subst Ks0
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp) f₁
          hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) ↔
            UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") [] "keep" w := by
          intro w; simp [UpdSemD]
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp, Or.inl ⟨rfl, emp⟩⟩
          cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
      · have KsNe : Ks ≠ [] := fun e => by
          obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil Ds d0
          have := (memKs d).mpr md; rw [e] at this; cases this
        have hA' : "atom" ∉ Ks := fun m => hna ((memKs _).mp m)
        obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) ef.none Bool.true hmd Ks hA' subKs lines hl'
        have sW := wlg_sem ef hl' (nt := .map []) Bool.true (Or.inl rfl) hmd hA' subKs KsNe
        have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
          cases Ds with
          | nil => exact absurd rfl d0
          | cons _ _ => simp [Term.list]
        rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, neR, lc, fc, sc⟩
        · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [] (by simp)
            f₁ hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
          have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) ↔
              UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "keep" w := by
            intro w
            simp only [UpdSemD, List.not_mem_nil, false_and, exists_false, false_or, true_and, reduceCtorEq,
              or_false, ← sW]
            exact ⟨Or.inl, fun h => h.elim id fun ⟨_, h'⟩ => absurd h' (emp w)⟩
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW] at rN1 rN2 ⊢ <;>
              simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW] at rN1 rN2 ⊢ <;>
              simp [rN1, rN2, rr]
        · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail_del (st := st) ef hn hmd lines hl A [c]
            (by simpa using fc) f₁ hT₁ (Term.list errs) (.atom "true") (Or.inl rfl)
          have sem : ∀ w, ((∃ b ∈ [c], denMF E den b w = Bool.true) ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) ↔
              UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks "keep" w := by
            intro w
            simp only [UpdSemD, List.mem_singleton, exists_eq_left, sc, sW, reduceCtorEq, false_and, exists_false,
              or_false, true_and, KsNe, ne_eq, not_false_eq_true]
            exact or_comm
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
              getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
              getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


/-- `map_update_static_dnf/6` deleting a key at the atoms outside a negated set and some kinds, asking for the old
values. -/
theorem upd_dnf_neg_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT [] (.map N) (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm md) := by
  classical
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have mk0 : Erlang.erlang.«++/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using append_list (ks.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl ([] ++ ks)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), .nil]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3»]
    simpa [Erlang.erlang.«++/2»] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), .nil]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), .nil]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  rcases hmd with rfl | rfl | rfl
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR', Lynx.Except.andAlso]
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
      simpa using length_list (Ks.map Term.atom)
    have fullI : Ks.length = 12 ↔ FullK Ks := by
      rw [lenKs]
      exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "force"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "force" Ws w) →
        ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := by
      intro Bx Ws SB SW hB hW hc w
      rw [hB, hW]
      rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · simp [UpdSemD, hf]
      · simp [UpdSemD, hf]
    -- The descr: the box, and the widened kinds.
    have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
        (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
        ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "force")
          (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Bx) := by
      intro Bx sub hf hnf
      have hAt : "atom" ∈ Bx ∨ ("force" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
        by_cases ak : "atom" ∈ Ks
        · left
          by_cases full : FullK Ks
          · rw [hf full]; exact ak
          · rw [hnf full]; simp [ak]
        · exact absurd aK ak
      have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
        by_cases full : FullK Ks
        · rw [hf full, fullI]; exact Iff.rfl
        · rw [hnf full]
          constructor
          · intro h
            have : (Ks.filter (· = "atom")).length ≤ 1 := by
              have nd := ndKs.filter (fun x => decide (x = "atom"))
              have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                simpa using (List.mem_filter.mp m).2
              generalize Ks.filter (· = "atom") = l at nd all
              match l, nd, all with
              | [], _, _ => simp
              | [_], _, _ => simp
              | x :: y :: t, nd, all =>
                exfalso
                have ex := all x List.mem_cons_self
                have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
            omega
          · intro h
            have := h "binary" (by simp [domainKinds])
            simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inl rfl) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
        (fun d md => subKs d (sub d md)) hAt hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    simp [dne', o1, o2, rKs, Erlang.erlang.«element/2», lenK,
      Lynx.Term.compare_integers]
    by_cases full : FullK Ks
    · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
      obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := fun w => by
        have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
        simpa using this
      simp [hL', rZ, Term.list]
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
          ks [] (by simp) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
            rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
          ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
            rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]

    · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
      have part := partition_atom (n + 5) Ks
      obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
        (fun h => absurd h full) (fun _ => rfl)
      have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
      have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      simp [hL', part, rX]
      by_cases wn : Ks.filter (· ≠ "atom") = []
      · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
        simp [wn', Term.list]
        have MZ := mX
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w => by
          have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
            (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          simpa using this
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
            ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
              rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
            ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
              rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]


      · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inl rfl)
          (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
        obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
        have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
          cases h : Ks.filter (· ≠ "atom") with
          | nil => exact absurd h wn
          | cons d ds => simp [Term.list]
        simp at wsCmp rW
        simp [wsCmp, rW, rZ]
        have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
            "force" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w =>
          semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
            (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
            ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
              rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inl rfl) lines hl
            ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force") fun w => by
              rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ ("keep" ≠ "reject" ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memK0 d
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have full : ¬("keep" ≠ "keep" ∧ FullK Ks) := fun h => h.1 rfl
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "keep"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "keep" Ws w) →
        Bx = Ks.filter (· = "atom") → Ws = Ks.filter (· ≠ "atom") →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w := by
      intro Bx Ws SB SW hB hW eB eW w
      subst eB eW
      rw [hB, hW]
      simp [UpdSemD]
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have part := partition_atom (n + 5) Ks
    obtain ⟨X, rX, mX⟩ : ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list ((Ks.filter (· = "atom")).map Term.atom)) (cOp (.map []) Bool.true "keep")
        (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom"))) := by
      have hlen : (Ks.filter (· = "atom")).length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ks.filter (· = "atom") := by
        constructor
        · intro h
          have : (Ks.filter (· = "atom")).length ≤ 1 := by
            have nd := ndKs.filter (fun x => decide (x = "atom"))
            have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
              simpa using (List.mem_filter.mp m).2
            generalize Ks.filter (· = "atom") = l at nd all
            match l, nd, all with
            | [], _, _ => simp
            | [_], _, _ => simp
            | x :: y :: t, nd, all =>
              exfalso
              have ex := all x List.mem_cons_self
              have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
              exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
          omega
        · intro h
          have := h "binary" (by simp [domainKinds])
          simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inl rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' (Ks.filter (· = "atom"))
        (fun d m => subKs d (List.mem_filter.mp m).1) (Or.inl (by simp [aK])) hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
    have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    simp [dne', rKs, Erlang.erlang.«element/2», part, rX, o1, o2]
    by_cases wn : Ks.filter (· ≠ "atom") = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
      simp [wn', Term.list]
      have MZ := mX
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w => by
        have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
          (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) rfl rfl w
        simpa using this
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inl rfl)) lines hl
          ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep") fun w => by
            rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inl rfl)) lines hl
          ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep") fun w => by
            rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


    · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
      obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
      have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
        cases h : Ks.filter (· ≠ "atom") with
        | nil => exact absurd h wn
        | cons d ds => simp [Term.list]
      simp at wsCmp rW
      simp [wsCmp, rW, rZ]
      have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
          "keep" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w =>
        semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
          (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) rfl rfl w
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inl rfl)) lines hl
          ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep") fun w => by
            rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inl rfl)) lines hl
          ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep") fun w => by
            rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨-, NK, -, -, -, -, -, lnNK, -⟩ := box_named (E := E) (n + 1) lines hl' AK
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, (kind_held ef hl hne lnNK (hDs d ms)).mpr h⟩
      · rintro ⟨ms, h⟩
        exact ⟨d, ms, rfl, (kind_held ef hl hne lnNK (hDs d ms)).mp h⟩
    have noAtom : "atom" ∉ Ks → ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x := fun na L mL x hx =>
      na ((memKs _).mpr ⟨hat, (kind_held ef hl hne lnNK (hDs _ hat)).mpr ⟨L, mL, x, hx⟩⟩)
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      have part := partition_atom (n + 5) []
      simp only [List.map_nil, List.filter_nil] at part
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' [] (by simp)
        (Or.inr ⟨rfl, noAtom (by simp)⟩)
        ⟨fun h => by simp at h, fun h => by simpa using h "atom" (by simp [domainKinds])⟩
      replace rX : Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) .nil (cOp (.map []) Bool.true "reject") (Term.list (AK.map Term.atom)) = .ok (.map X) := by
        exact rX
      simp [Term.list, boolAtom, Lynx.Except.orElse,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
          [] w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemD, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
          ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject") fun w => by
            rw [sB', ← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
          ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject") fun w => by
            rw [sB', ← semB]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        have mapE : Term.map X ≠ Term.map [] := fun e => neX (by injection e)
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
        simpa using length_list (Ks.map Term.atom)
      have fullI : Ks.length = 12 ↔ FullK Ks := by
        rw [lenKs]
        exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
      have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
          (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
            Bx w) →
          (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "reject" Ws w) →
          ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
          ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := by
        intro Bx Ws SB SW hB hW hc w
        rw [hB, hW]
        rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
        · simp [UpdSemD, hf]
        · simp [UpdSemD, hf]
      -- The descr: the box, and the widened kinds.
      have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
          (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
          ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
            (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "reject")
            (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
          MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Bx) := by
        intro Bx sub hf hnf
        have hAt : "atom" ∈ Bx ∨ ("reject" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
          by_cases ak : "atom" ∈ Ks
          · left
            by_cases full : FullK Ks
            · rw [hf full]; exact ak
            · rw [hnf full]; simp [ak]
          · exact Or.inr ⟨rfl, noAtom ak⟩
        have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
          by_cases full : FullK Ks
          · rw [hf full, fullI]; exact Iff.rfl
          · rw [hnf full]
            constructor
            · intro h
              have : (Ks.filter (· = "atom")).length ≤ 1 := by
                have nd := ndKs.filter (fun x => decide (x = "atom"))
                have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                  simpa using (List.mem_filter.mp m).2
                generalize Ks.filter (· = "atom") = l at nd all
                match l, nd, all with
                | [], _, _ => simp
                | [_], _, _ => simp
                | x :: y :: t, nd, all =>
                  exfalso
                  have ex := all x List.mem_cons_self
                  have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                  exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
              omega
            · intro h
              have := h "binary" (by simp [domainKinds])
              simp at this
        obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
          (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
          (fun d md => subKs d (sub d md)) hAt hlen
        refine ⟨X, ?_, mX⟩
        exact rX
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, Erlang.erlang.«element/2», lenK,
        Lynx.Term.compare_integers]
      by_cases full : FullK Ks
      · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
        obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := fun w => by
          have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
          simpa using this
        simp [hL', rZ, Term.list]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
            ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
              rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
            ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
              rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]

      · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
        have part := partition_atom (n + 5) Ks
        obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
          (fun h => absurd h full) (fun _ => rfl)
        have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
        have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
        simp [hL', part, rX]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          have MZ := mX
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
              ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
                rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
              ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
                rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


        · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inr rfl))
            (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
          obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp at wsCmp rW
          simp [wsCmp, rW, rZ]
          have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
              "reject" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w =>
            semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
              (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
              ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
                rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg_del (st := st) ef hn (Or.inr (Or.inr rfl)) lines hl
              ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemD den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject") fun w => by
                rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static_dnf/6` deleting a key at a split of keys. -/
theorem upd_dnf_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) rk neg Dm md) := by
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · have hna : "atom" ∉ Ds := fun m => by
      obtain ⟨N, e⟩ := ok.hatom.mp (List.mem_map_of_mem m); cases e
    exact upd_dnf_nil_del (st := st) ef hn hmd bdd lines hl hne rk Ds hDs hna
  · obtain rfl := nr N rfl
    obtain ⟨hNa, ks, hR, hks, lnKS⟩ := hneg N rfl
    have hat : "atom" ∈ Ds := by
      have := ok.hatom.mpr ⟨N, rfl⟩
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    exact upd_dnf_neg_del (st := st) ef hn hmd bdd fbd lines hl hne sbd N hNa ks hR hks lnKS Ds hDs hat

/-- `map_update_static/5` deleting a key at a split of keys, asking for the old values. -/
theorem del_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md) (st : Bool)
    {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (UpdSemD den (fun u => denMF E den b u = Bool.true) rk neg Dm md)) := by
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
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ := upd_dnf_del (st := st) ef hn hmd (.tuple #[.integer k, tag, fieldsTerm l])
        fb _ hl (by simp) inB ok nr hneg
      rw [conv inB] at hY mDm
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      simpa [Term.list, boolAtom] using rY
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
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ := upd_dnf_del (st := st) ef hn hmd b fb (L :: rest) hl (by simp) inB ok nr
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

/-- `map_update/5` deleting a key at a static key type, asking for the old values, in static types of the next level:
`:badmap`, an error, or the maps `UpdSemD` gives. -/
theorem del_update {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {md : String} (hmd : Mode md)
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.atom "delete") (.atom md) (.atom "true") = .ok r ∧
      (r = .atom "badmap" ∨ (∃ er, r = .tuple #[.atom "error", er]) ∨
        ∃ T Y er, r = .tuple #[T, .map Y, er] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) ∧
            ∀ w, MT t n Y w ↔ UpdSemD (level t n).den (MT t n X) rk neg Dm md w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D (k + 6)) (.map X) key (.atom "delete") (.atom md)
      (.atom "true") = Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«map_update/5»
    rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk] <;> rfl
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
        del_update_static (st := Bool.true) (level t n).ef (n := k) (by omega) hmd ok nr hNa hb fb
      all_goals simp only [boolAtom, ↓reduceIte] at run
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

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-! Monotonicity of the maps of `map_update/5` deleting a key. -/

/-- A deletion puts no value. -/
theorem newF_del_some (nn : ∀ x, ¬den (.map []) x) {md : String} {O : Option V → Prop} (x : V) :
    ¬NewF den (.map []) Bool.true md O (some x) := by
  unfold NewF
  intro h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rcases h with ⟨h, -⟩ | ⟨y, e, hy⟩
    · cases h
    · cases e; exact nn _ hy
  · rcases h with ⟨-, ⟨h, -⟩ | ⟨y, e, hy⟩⟩ | ⟨-, h⟩
    · cases h
    · cases e; exact nn _ hy
    · cases h

theorem newDomS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {md d : String} {x : V} :
    ¬NewDomS den M (.map []) md d x := fun h => nn x h.1

/-- Whether a deletion's updates hold old values or new ones only depends on the old ones. -/
theorem updHasS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {S : List String} {md : String}
    {Ds : List String} {A : Prop → Prop → Prop} :
    UpdHasS den M S (.map []) Bool.true md Ds A ↔ UpdHasS den M S (.map []) Bool.true md Ds (fun o _ => A o False) := by
  have n₁ : ∀ s, (∃ x, NewF den (.map []) Bool.true md (Old M (.atom s)) (some x)) = False := fun s =>
    propext ⟨fun ⟨x, h⟩ => newF_del_some nn x h, False.elim⟩
  have n₂ : ∀ d, (∃ x, NewDomS den M (.map []) md d x) = False := fun d =>
    propext ⟨fun ⟨x, h⟩ => newDomS_del nn h, False.elim⟩
  unfold UpdHasS
  simp only [n₁, n₂]

/-- Not keeping, a deletion's box is never present. -/
theorem presentS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {S : List String} {md : String}
    {Ds : List String} (hk : md ≠ "keep") : ¬PresentS den M S (.map []) Bool.true md Ds := by
  intro h
  have := (updHasS_del nn).mp (h.2 hk)
  rcases this with ⟨_, _, h'⟩ | ⟨_, _, _, _, h'⟩ <;> exact h'

theorem delAt_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md a : String} {w : MW V}
    (h : DelAt M₁ md a w) : DelAt M₂ md a w :=
  ⟨h.1, h.2.imp (fun ⟨x, hx⟩ => ⟨x, hM _ hx⟩) fun ⟨hr, hw⟩ => ⟨hr, hM _ hw⟩⟩

theorem wres_mono_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V} (h : WRes den M₁ (.map []) md Ds₁ w) :
    WRes den M₂ (.map []) md Ds₂ w := by
  obtain ⟨hs, -⟩ := h
  refine ⟨fun F => ?_, fun ⟨x, hx⟩ => absurd hx (nn x)⟩
  obtain ⟨u, hu, hr, a⟩ := hs F
  exact ⟨u, hM u hu, fun r => let ⟨d, md', hk⟩ := hr r; ⟨d, hD d md', hk⟩, agreeP_mono hD (fun d x h => h) a⟩

/-- The box of a deletion is monotone in the type, the atoms of the key type and the kinds. -/
theorem boxSem_mono_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u)
    {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁) {md : String} {Ds₁ Ds₂ : List String}
    (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V}
    (h : BoxSem den M₁ S₁ (.map []) Bool.true md Ds₁ w) : BoxSem den M₂ S₂ (.map []) Bool.true md Ds₂ w := by
  have hv : ∀ x, den (.map []) x → den (.map []) x := fun _ h => h
  obtain ⟨pre₁, hs₁, hn₁⟩ := h
  have pre₂ := updHasS_mono hM hS hv hD (A₁ := fun _ _ => True) (A₂ := fun _ _ => True) (fun _ _ _ _ _ _ h => h) pre₁
  have rs : ∀ s, RS den M₂ S₂ (.map []) Bool.true md Ds₂ s → RS den M₁ S₁ (.map []) Bool.true md Ds₁ s := by
    rintro s ⟨hr, nd, hk, uq⟩
    have nd₁ : ∀ d ∈ Ds₁, d ≠ "atom" → ¬DomNES den M₁ (.map []) Bool.true md d := fun d md' da h' =>
      nd d (hD d md') da (domNES_mono hM hv h')
    rcases pre₁ with ⟨s', hk', -⟩ | ⟨d, md', da, hne, -⟩
    · have := uq s' (keyNES_mono hM hS hv hk')
      subst this
      exact ⟨hr, nd₁, hk', fun s'' h'' => uq s'' (keyNES_mono hM hS hv h'')⟩
    · exact absurd hne (nd₁ d md' da)
  -- Old values of a key or kind of the box.
  have olds : UpdHasS den M₁ S₁ (.map []) Bool.true md Ds₁ (fun o _ => o) →
      UpdHasS den M₂ S₂ (.map []) Bool.true md Ds₂ (fun o _ => o) := fun h =>
    updHasS_mono hM hS hv hD (A₁ := fun o _ => o) (A₂ := fun o _ => o) (fun _ _ _ _ ho _ h => ho h) h
  refine ⟨pre₂, fun hs₂ => ?_, fun ns₂ => ?_⟩
  · have hs₁' : SameS den M₁ S₁ (.map []) Bool.true md Ds₁ := ⟨hs₂.1, fun h' => hs₂.2 (updHasS_mono hM hS hv hD
      (A₁ := fun o n => o ∨ n) (A₂ := fun o n => o ∨ n) (fun _ _ _ _ ho hn h => h.imp ho hn) h')⟩
    exact hM w (hs₁ hs₁')
  -- A present box: only when keeping, and then the type lacks the empty map, as does the box of the smaller one.
  have pres : PresentS den M₂ S₂ (.map []) Bool.true md Ds₂ → md = "keep" ∧ ¬M₂ wNone ∧
      PresentS den M₁ S₁ (.map []) Bool.true md Ds₁ := fun hp => by
    by_cases hk : md = "keep"
    · obtain ⟨nl, n0⟩ := hp.1 hk
      refine ⟨hk, n0, fun _ => ⟨fun h' => nl ?_, fun h0 => n0 (hM _ h0)⟩, fun h' => absurd hk h'⟩
      exact (updHasS_del nn).mpr (by
        have := olds (by
          have := (updHasS_del nn).mp h'
          exact updHasS_mono (fun u h => h) (fun s h => h) hv (fun d h => h) (A₁ := fun o _ => o ∧ ¬False)
            (A₂ := fun o _ => o) (fun _ _ _ _ ho _ h => ho h.1) this)
        exact updHasS_mono (fun u h => h) (fun s h => h) hv (fun d h => h) (A₁ := fun o _ => o)
          (A₂ := fun o _ => o ∧ ¬False) (fun _ _ _ _ ho _ h => ⟨ho h, id⟩) this)
    · exact absurd hp (presentS_del nn hk)
  by_cases sm₁ : SameS den M₁ S₁ (.map []) Bool.true md Ds₁
  · have wM := hM w (hs₁ sm₁)
    have hk : md = "keep" := sm₁.1
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp at this
    · cases e : w (.dom k i) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl, Or.inl ⟨w, k, i, wM, rfl, e⟩⟩
    · rintro rfl; exact (pres hp).2.1 wM
  obtain ⟨⟨ha, hd⟩, hq⟩ := hn₁ sm₁
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
  · rcases ha s with ⟨sS1, h⟩ | ⟨nS1, ⟨nr, h⟩ | h⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, old_mono hM h⟩
      · exact Or.inr ⟨sS, Or.inl ⟨fun r => (rs s r).2.2.1.1 sS1, old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inl ⟨fun r => nr (rs s r), old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inr (newF_mono hv (fun _ => old_mono hM) h)⟩
  · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, Or.inl (kindVal_mono hM hx)⟩
    · exact Or.inr ⟨x, h, Or.inr ⟨hD _ dk, newDomS_mono hM hv hx⟩⟩
  · exact (hq (pres hp).2.2).2 fun c => absurd c.1 (by simp)

/-- A deletion at a named atom of the key type gives maps of the box. -/
theorem del_box (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) {S : List String} {Ds : List String} {a : String} (ha : a ∉ S) {w : MW V}
    (h : DelAt M₁ md a w) : BoxSem den M₂ S (.map []) Bool.true md Ds w := by
  obtain ⟨wa, h⟩ := h
  -- The key's old field and its update.
  have keyA : KeyNES den M₂ S (.map []) Bool.true md a := by
    refine ⟨ha, none, ?_⟩
    rcases h with ⟨y, hy⟩ | ⟨hr, hw⟩
    · exact Or.inl ⟨⟨y, _, hM _ hy, by simp [setK]⟩, Or.inl ⟨rfl, rfl⟩⟩
    · refine Or.inr ⟨⟨w, hM _ hw, wa⟩, ?_⟩
      rcases hmd with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hr
  have notR : ∀ s, s ≠ a → ¬RS den M₂ S (.map []) Bool.true md Ds s := fun s ne r => ne (r.2.2.2 a keyA).symm
  refine ⟨Or.inl ⟨a, keyA, trivial⟩, fun hs => ?_, fun ns => ?_⟩
  · rcases h with ⟨y, hy⟩ | ⟨-, hw⟩
    · exact absurd (Or.inl ⟨a, keyA, Or.inl ⟨y, _, hM _ hy, by simp [setK]⟩⟩) hs.2
    · exact hM _ hw
  rcases h with ⟨y, hy⟩ | ⟨hr, hw⟩
  · -- The key held a value.
    have u₀ := hM _ hy
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sa : s = a
      · subst sa
        refine Or.inr ⟨ha, Or.inr ?_⟩
        rw [wa]
        exact Or.inl ⟨⟨y, _, u₀, by simp [setK]⟩, Or.inl ⟨rfl, rfl⟩⟩
      · have ew : w (.atom s) = setK a (some y) w (.atom s) := by simp [setK, sa]
        by_cases sS : s ∈ S
        · exact Or.inl ⟨sS, _, u₀, ew.symm⟩
        · exact Or.inr ⟨sS, Or.inl ⟨notR s sa, _, u₀, ew.symm⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨_, k, i, u₀, rfl, by simp [setK, e']⟩⟩
    · -- A present box keeps no key with old values.
      by_cases hk : md = "keep"
      · exact absurd ((updHasS_del nn).mpr (Or.inl ⟨a, keyA, ⟨y, _, u₀, by simp [setK]⟩, id⟩)) (hp.1 hk).1
      · exact absurd hp (presentS_del nn hk)
  · -- Not rejecting, a map lacking the key.
    have wM := hM _ hw
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · exact Or.inr ⟨sS, Or.inl ⟨fun r => hr r.1, w, wM, rfl⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨w, k, i, wM, rfl, e'⟩⟩
    · by_cases hk : md = "keep"
      · rintro rfl; exact (hp.1 hk).2 wM
      · exact absurd hp (presentS_del nn hk)

/-- Not keeping, with every kind in the box: the widened kinds of a deletion give maps of the box. -/
theorem widen_box_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) (hk : md ≠ "keep") {S Ws Ds : List String} (hA : "atom" ∉ Ws) (neW : Ws ≠ [])
    (hD : ∀ d ∈ Ws, d ∈ Ds) {w : MW V}
    (h : WRes den M₁ (.map []) md Ws w) : BoxSem den M₂ S (.map []) Bool.true md Ds w := by
  obtain ⟨hs, -⟩ := h
  obtain ⟨u₀, hu₀, hr₀, a₀⟩ := hs []
  -- An updated kind other than atoms.
  obtain ⟨d₀, md₀, dne⟩ : ∃ d₀ ∈ Ws, DomNES den M₂ (.map []) Bool.true md d₀ := by
    rcases hmd with rfl | rfl | rfl
    · obtain ⟨d₀, md₀⟩ := List.exists_mem_of_ne_nil Ws neW
      exact ⟨d₀, md₀, Or.inr ⟨Or.inl rfl, Or.inl rfl⟩⟩
    · exact absurd rfl hk
    · obtain ⟨d₀, md₀, hk₀⟩ := hr₀ rfl
      have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
      exact ⟨d₀, md₀, Or.inr ⟨Or.inr ⟨fun e => absurd e da, fun _ => ⟨u₀, hM _ hu₀, hk₀⟩⟩, Or.inl rfl⟩⟩
  have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
  refine ⟨Or.inr ⟨d₀, hD d₀ md₀, da, dne, trivial⟩, fun hs' => absurd hs'.1 hk, fun _ => ?_⟩
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => absurd hp (presentS_del nn hk)⟩
  · by_cases sS : s ∈ S
    · exact Or.inl ⟨sS, u₀, hM _ hu₀, (a₀.1 s).symm⟩
    · exact Or.inr ⟨sS, Or.inl ⟨fun r => r.2.1 d₀ (hD d₀ md₀) da dne, u₀, hM _ hu₀, (a₀.1 s).symm⟩⟩
  · obtain ⟨u, hu, -, a⟩ := hs [.dom k i]
    have kv : ∀ o, o = u (.dom k i) → w (.dom k i) = o → w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧
        (KindVal M₂ (domKind k) x ∨ (domKind k ∈ Ds ∧ NewDomS den M₂ (.map []) md (domKind k) x)) := by
      intro o eo ew
      subst eo
      cases e' : u (.dom k i) with
      | none => exact Or.inl (ew.trans e')
      | some z => exact Or.inr ⟨z, ew.trans e', Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩
    by_cases dk : domKind k ∈ Ws
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx, -⟩
      · exact Or.inl e
      · exact kv _ rfl e
      · exact absurd hx (nn x)
    · exact kv _ rfl (a.2.1 k i dk)

/-- `map_update/5` deleting a key is monotone in the type and the keys. -/
theorem del_mono (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) {rs₁ rs₂ Ds₁ Ds₂ Dm₁ Dm₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hDm₁ : ∀ d, d ∈ Dm₁ ↔ d ∈ Ds₁ ∧ (md ≠ "reject" ∨ KindHeld M₁ d))
    (hDm₂ : ∀ d, d ∈ Dm₂ ↔ d ∈ Ds₂ ∧ (md ≠ "reject" ∨ KindHeld M₂ d)) {w : MW V}
    (h : UpdSemD den M₁ rs₁ neg₁ Dm₁ md w) : UpdSemD den M₂ rs₂ neg₂ Dm₂ md w := by
  classical
  have hD₁ : ∀ s ∈ Ds₁, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok₁.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  -- The kinds of the small split are kinds of the large one.
  have dsub : ∀ d ∈ Ds₁, d ∈ Ds₂ := by
    intro d md
    by_cases da : d = "atom"
    · subst da
      obtain ⟨N₁, e₁⟩ := ok₁.hatom.mp (List.mem_map_of_mem md)
      subst e₁
      obtain ⟨c, hc⟩ := fresh_str (keyStrs N₁ ++ rs₂)
      have k₂ := hK (.atom c) (Or.inr ⟨N₁, rfl, lookup_fresh' fun m => hc (List.mem_append_left _ m)⟩)
      rcases k₂ with m | ⟨N₂, e₂, -⟩
      · obtain ⟨c', mc', e⟩ := List.mem_map.mp m
        cases e; exact absurd (List.mem_append_right _ mc') hc
      · have := ok₂.hatom.mpr ⟨N₂, e₂⟩
        obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    · obtain ⟨k, rfl⟩ := domKind_of (hD₁ _ md) da
      have := hK (.dom k 0) (List.mem_map_of_mem md)
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
  have dmsub : ∀ d ∈ Dm₁, d ∈ Dm₂ := fun d m => by
    obtain ⟨md, h'⟩ := (hDm₁ d).mp m
    exact (hDm₂ d).mpr ⟨dsub d md, h'.imp id (kindHeld_mono hM)⟩
  have fullM : FullK Dm₁ → FullK Dm₂ := fun f d m => dmsub d (f d m)
  have filt : ∀ (p : String → Bool) d, d ∈ Dm₁.filter p → d ∈ Dm₂.filter p := fun p d m => by
    rw [List.mem_filter] at m ⊢; exact ⟨dmsub d m.1, m.2⟩
  -- The atoms of the small split are atoms of the large one.
  have named : ∀ a ∈ rs₁, (neg₂ = .atom "nil" → a ∈ rs₂) ∧ ∀ N₂, neg₂ = .map N₂ → a ∉ setStrs N₂ := by
    intro a ma
    have k₂ := hK (.atom a) (Or.inl (List.mem_map_of_mem ma))
    refine ⟨fun e => ?_, fun N₂ e => ?_⟩
    · rcases k₂ with m | ⟨N, e', -⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp m; cases e; exact ma'
      · rw [e] at e'; cases e'
    · rcases k₂ with m | ⟨N, e', hN⟩
      · rw [nr₂ N₂ e] at m; simp at m
      · rw [e] at e'; cases e'; exact fun m => setStrs_mem.mp m hN
  rcases h with ⟨rfl, hn | ⟨dne, hw⟩⟩ | ⟨N₁, rfl, h⟩
  · -- An atom of the small split.
    obtain ⟨a, ma, ha⟩ := hn
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl ⟨a, (named a ma).1 rfl, delAt_mono hM ha⟩⟩
    · have hb := fun Ds => del_box (Ds := Ds) nn hM hmd ((named a ma).2 N₂ rfl) ha
      by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, hb Dm₂⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (hb _)⟩⟩
  · -- The widened kinds of the small split.
    have nA : "atom" ∉ Dm₁ := fun m => by
      obtain ⟨N, e⟩ := ok₁.hatom.mp (List.mem_map_of_mem ((hDm₁ _).mp m).1); cases e
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ⟨fun e => dne ?_, wres_mono_del nn hM dmsub hw⟩⟩
      cases Dm₁ with
      | nil => rfl
      | cons d _ => have := dmsub d List.mem_cons_self; rw [e] at this; cases this
    · by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, widen_box_del nn hM hmd kf nA dne dmsub hw⟩⟩
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => dne ?_, wres_mono_del nn hM (fun d m => ?_) hw⟩⟩⟩
        · cases Dm₁ with
          | nil => rfl
          | cons d _ =>
            have := filt (fun x => decide (x ≠ "atom")) d (by
              simp only [List.mem_filter, List.mem_cons_self, true_and, decide_eq_true_eq]
              exact fun e' => nA (e' ▸ List.mem_cons_self))
            rw [e] at this; cases this
        · exact filt (fun x => decide (x ≠ "atom")) d (List.mem_filter.mpr ⟨m, by
            simp only [decide_eq_true_eq]; exact fun e' => nA (e' ▸ m)⟩)
  · -- The box and the widened kinds of a negated set.
    have at₁ : "atom" ∈ Ds₁ := by
      have := ok₁.hatom.mpr ⟨N₁, rfl⟩
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    obtain ⟨N₂, e₂⟩ : ∃ N₂, neg₂ = .map N₂ := ok₂.hatom.mp (List.mem_map_of_mem (dsub _ at₁))
    subst e₂
    have hS : ∀ s, s ∈ setStrs N₂ → s ∈ setStrs N₁ := fun s m => Classical.byContradiction fun nm => by
      have hN₁ : mapLookup N₁ (.atom s) = none := by
        cases e : mapLookup N₁ (.atom s) with
        | none => rfl
        | some _ => exact absurd (setStrs_mem.mpr (by rw [e]; simp)) nm
      have k₂ := hK (.atom s) (Or.inr ⟨N₁, rfl, hN₁⟩)
      rcases k₂ with m' | ⟨N, e, hN⟩
      · rw [nr₂ N₂ rfl] at m'; simp at m'
      · cases e; exact setStrs_mem.mp m hN
    have bm := fun {Ds₁' Ds₂' : List String} (hD : ∀ d ∈ Ds₁', d ∈ Ds₂') {w : MW V}
      (h : BoxSem den M₁ (setStrs N₁) (.map []) Bool.true md Ds₁' w) =>
      boxSem_mono_del nn hM hS hD h
    rcases h with ⟨kf, full, hb⟩ | ⟨nf, hb | ⟨wne, hw⟩⟩
    · exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, fullM full, bm dmsub hb⟩⟩
    · by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, bm (fun d m => dmsub d (List.mem_filter.mp m).1) hb⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (bm (filt _) hb)⟩⟩
    · have nA : "atom" ∉ Dm₁.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, widen_box_del nn hM hmd kf nA wne
          (fun d m => dmsub d (List.mem_filter.mp m).1) hw⟩⟩
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => wne ?_, wres_mono_del nn hM (filt _) hw⟩⟩⟩
        cases h' : Dm₁.filter (· ≠ "atom") with
        | nil => rfl
        | cons d _ =>
          have := filt _ d (by rw [h']; exact List.mem_cons_self)
          rw [e] at this; cases this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Two successful `map_update/5` deleting static key types, asking for the old values, on static maps of the next
level: a smaller type and smaller keys give fewer maps. -/
theorem del_sub {XL XR : List (Term × Term)} (hXL : DE (level t n).E (.map XL)) (hXR : DE (level t n).E (.map XR))
    (maps : ∀ w, MT t n XL w → MT t n XR w) {k₁ k₂ : Term} {rs₁ rs₂ Ds₁ Ds₂ : List String} {neg₁ neg₂ : Term}
    {m : Nat}
    (rk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ =
      .ok (splitT (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)))
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (nr₁ : ∀ N, neg₁ = .map N → rs₁ = [])
    (na₁ : ∀ N, neg₁ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (rk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ =
      .ok (splitT (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)))
    (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)) (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (na₂ : ∀ N, neg₂ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (keys : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    {md : String} (hmd : Mode md) (hm : (level t n).K + 26 ≤ m)
    {T₁ Y₁ e₁ T₂ Y₂ e₂ : Term}
    (run₁ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XL) k₁ (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T₁, Y₁, e₁]))
    (run₂ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XR) k₂ (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T₂, Y₂, e₂])) :
    ∃ YL YR, Y₁ = .map YL ∧ Y₂ = .map YR ∧ DE (level t n).E (.map YL) ∧ DE (level t n).E (.map YR) ∧
      SubN t n (.map YL) (.map YR) := by
  have side : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
      {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
        .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
      (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
      (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {T Y e : Term}
      (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T, Y, e])),
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) ∧
          ∀ w, MT t n Y' w ↔ UpdSemD (level t n).den (MT t n X) rs neg Dm md w := by
    intro X hX k rs Ds neg rk ok nr na T Y e run
    obtain ⟨r, rr, rfl | ⟨er, rfl⟩ | ⟨T', Y', er, rfl, -, dY, oY, Dm, mDm, sY⟩⟩ := del_update hX rk ok nr na hmd hm
    · rw [run] at rr; cases rr
    · rw [run] at rr; cases rr
    · rw [run] at rr
      obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj rr)
      exact ⟨Y', rfl, dY, oY, Dm, mDm, sY⟩
  obtain ⟨YL, rfl, dL, oL, Dm₁, mDm₁, sL⟩ := side hXL rk₁ ok₁ nr₁ na₁ run₁
  obtain ⟨YR, rfl, dR, -, Dm₂, mDm₂, sR⟩ := side hXR rk₂ ok₂ nr₂ na₂ run₂
  refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
  obtain ⟨w, hw⟩ := pt_map q (oL q hq)
  rw [hw] at hq ⊢
  exact (sR w).mpr (del_mono (fun x => (level t n).ef.den_none x) maps hmd ok₁ ok₂ nr₂ keys mDm₁ mDm₂ ((sL w).mp hq))

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Whether `map_update/5` finds the keys it updates, and the domains it reports missing. -/

/-- `map_update_get_domains/5` finds a domain some line holds, or the atom domain when the callback finds a named atom
key, and reports the domains no line holds missing. -/
theorem upd_found (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (cb : Term) (c : Bool) (hc : (D (n + 3)).pure cb #[] = .ok (boolAtom c))
    (Ds : List String) {acc : Term} (ha : E acc) :
    ∃ (f : Bool) (val mis : List Term) (T : Term),
      Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 4)) (Term.list lines) (Term.list (Ds.map Term.atom))
        acc (.atom "true") cb = .ok (.tuple #[boolAtom f, Term.list val, Term.list mis, T]) ∧
      (f = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨ ("atom" ∈ Ds ∧ c = Bool.true)) ∧
      ∀ d, d ∈ mis ↔ ∃ s ∈ Ds, d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x := by
  obtain ⟨r, ⟨f, val, mis, T, rfl, hT, fD, mD⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_get_domains/5-fun-0-" #[Term.list lines, .atom "true", cb]
    (fun pre a => ∃ (f : Bool) (val mis : List Term) (T : Term), a = .tuple #[boolAtom f, Term.list val, Term.list mis, T] ∧
      E T ∧ (f = Bool.true ↔ (∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        (.atom "atom" ∈ pre ∧ c = Bool.true)) ∧
      (∀ d, d ∈ mis ↔ ∃ s, .atom s ∈ pre ∧ d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x))
    (Ds.map Term.atom) (fun pre x a mx ⟨f, val, mis, T, ea, hT, fD, mD⟩ => by
      subst ea
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨g, rg, hg, sg⟩ := get_domain1 ef (n := n + 3) (by omega) lines hl s
      obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hg
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hT hg (m := n + 3) (by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5», rg, rb, Lynx.Except.ok_bind,
        Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«==/2», equal_eq_decide]
      have heldI : b = Bool.false ↔ ∃ L ∈ lines, ∃ x, LineTag den L s x := by
        constructor
        · intro hb
          subst hb
          obtain ⟨x, hx⟩ : ∃ x, den g x := Classical.byContradiction fun h => by
            have := sb.mpr fun y hy => h ⟨y, hy⟩; cases this
          obtain ⟨L, mL, hL⟩ := (sg x).mp hx
          exact ⟨L, mL, x, hL⟩
        · rintro ⟨L, mL, x, hx⟩
          cases b
          · rfl
          · exact absurd ((sg x).mpr ⟨L, mL, hx⟩) (sb.mp rfl x)
      -- The facts on the extended prefix.
      have memA : ∀ s', .atom s' ∈ pre ++ [Term.atom s] ↔ .atom s' ∈ pre ∨ s' = s := fun s' => by simp
      have fTrue : (∃ L ∈ lines, ∃ x, LineTag den L s x) → ((∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧
          ∃ L ∈ lines, ∃ x, LineTag den L s' x) ∨ (.atom "atom" ∈ pre ++ [Term.atom s] ∧ c = Bool.true)) :=
        fun h => Or.inl ⟨s, by simp, h⟩
      have fSame : (¬∃ L ∈ lines, ∃ x, LineTag den L s x) → (s ≠ "atom" ∨ c = Bool.false) →
          ((f = Bool.true) ↔ ((∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ ∃ L ∈ lines, ∃ x, LineTag den L s' x) ∨
            (.atom "atom" ∈ pre ++ [Term.atom s] ∧ c = Bool.true))) := fun nh hc' => by
        rw [fD]
        constructor
        · rintro (⟨s', m', h⟩ | ⟨m', hc''⟩)
          · exact Or.inl ⟨s', by simp [m'], h⟩
          · exact Or.inr ⟨by simp [m'], hc''⟩
        · rintro (⟨s', m', h⟩ | ⟨m', hc''⟩)
          · rcases (memA s').mp m' with m' | rfl
            · exact Or.inl ⟨s', m', h⟩
            · exact absurd h nh
          · rcases (memA "atom").mp m' with m' | e
            · exact Or.inr ⟨m', hc''⟩
            · rcases hc' with h | h
              · exact absurd e.symm h
              · rw [h] at hc''; cases hc''
      have misAdd : (¬∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ Term.atom s :: mis ↔
          ∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ d = .atom s' ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro nh d
        rw [List.mem_cons, mD]
        constructor
        · rintro (rfl | ⟨s', m', e, h⟩)
          · exact ⟨s, by simp, rfl, nh⟩
          · exact ⟨s', by simp [m'], e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases (memA s').mp m' with m' | rfl
          · exact Or.inr ⟨s', m', rfl, h⟩
          · exact Or.inl rfl
      have misKeep : (∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ mis ↔
          ∃ s', .atom s' ∈ pre ++ [Term.atom s] ∧ d = .atom s' ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro hh d
        rw [mD]
        constructor
        · rintro ⟨s', m', e, h⟩
          exact ⟨s', by simp [m'], e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases (memA s').mp m' with m' | rfl
          · exact ⟨s', m', rfl, h⟩
          · exact absurd hh h
      by_cases sa : s = "atom"
      · subst sa
        cases b
        · refine ⟨_, ⟨Bool.true, .atom "atom" :: val, mis, u, rfl, hu, ⟨fun _ => fTrue (heldI.mp rfl), fun _ => rfl⟩,
            misKeep (heldI.mp rfl)⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list]
        · have nh : ¬∃ L ∈ lines, ∃ x, LineTag den L "atom" x := fun h => by have := heldI.mpr h; cases this
          cases c
          · refine ⟨_, ⟨f, val, .atom "atom" :: mis, T, rfl, hT, fSame nh (Or.inr rfl), misAdd nh⟩, ?_⟩
            simp [boolAtom, Term.list, hc, Erlang.erlang.«/=/2»]
          · refine ⟨_, ⟨Bool.true, val, .atom "atom" :: mis, T, rfl, hT,
              ⟨fun _ => Or.inr ⟨by simp, rfl⟩, fun _ => rfl⟩, misAdd nh⟩, ?_⟩
            simp [boolAtom, Term.list, hc, Erlang.erlang.«/=/2»]
      · have ne : Term.compare (Term.fuel (.atom s) (.atom "atom")) (.atom s) (.atom "atom") ≠ .eq := by
          rw [atoms_cmp]; exact fun e => sa (Std.compare_eq_iff_eq.mp e)
        cases b
        · refine ⟨_, ⟨Bool.true, .atom s :: val, mis, u, rfl, hu, ⟨fun _ => fTrue (heldI.mp rfl), fun _ => rfl⟩,
            misKeep (heldI.mp rfl)⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list, ne]
        · have nh : ¬∃ L ∈ lines, ∃ x, LineTag den L s x := fun h => by have := heldI.mpr h; cases this
          refine ⟨_, ⟨f, val, .atom s :: mis, T, rfl, hT, fSame nh (Or.inl sa), misAdd nh⟩, ?_⟩
          simp [boolAtom, Term.list, ne])
    (.tuple #[.atom "false", .nil, .nil, acc]) ⟨Bool.false, [], [], acc, rfl, ha, by simp, by simp⟩
  refine ⟨f, val, mis, T, ?_, ?_, fun d => ?_⟩
  · simpa [Elixir.Module.Types.Descr.«map_update_get_domains/5», boolAtom, Term.list] using run
  · rw [fD]; simp
  · rw [mD]; simp

/-- `++/2` of a list and any term. -/
theorem append_any (a : List Term) (b : Term) :
    Erlang.erlang.«++/2» (Term.list a) b = .ok (a.foldr Term.cons b) := by
  induction a with
  | nil => simp [Erlang.erlang.«++/2»]
  | cons h t ih => simp [Erlang.erlang.«++/2»] at ih ⊢; simp [ih]

/-- `map_update_named_keys/8` for a constant, asking for the old values on a static type: the errors it adds are
`badkey` errors, and it finds a key when forcing, or when some map holds a value there and no map lacks it. -/
theorem named_flag (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (fld : Term) {md : String}
    (hmd : Mode md) (req st : Bool) (bd : Term)
    (hk : ∀ a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) bd (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) :
    ∀ (ks : List String) (T B : Term) (Er : List Term) (f : Bool), E T →
      ∃ (T' B' : Term) (extra : List Term) (f' : Bool),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, B, Term.list Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
          (boolAtom req) (boolAtom st) (.atom "true") bd =
          .ok (.tuple #[T', B', Term.list (extra ++ Er), boolAtom f']) ∧ E T' ∧
        (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ (md = "force" ∧ ks ≠ []) ∨
          ∃ a ∈ ks, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) := by
  have loop : ∀ (ks : List String) (T B : Term) (Er : List Term) (f : Bool), E T →
      ∃ (T' B' : Term) (extra : List Term) (f' : Bool),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, .tuple #[.tuple #[.atom "constant", fld], .atom md], boolAtom req, boolAtom st, bd,
              .atom "true", boolAtom (decide (md = "force"))])
          (.tuple #[T, B, Term.list Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', B', Term.list (extra ++ Er), boolAtom f']) ∧ E T' ∧
        (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ (md = "force" ∧ ks ≠ []) ∨
          ∃ a ∈ ks, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) := by
    intro ks
    induction ks with
    | nil =>
      intro T B Er f hT
      exact ⟨T, B, [], f, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, by simp, by simp⟩
    | cons a rest ih =>
      intro T B Er f hT
      obtain ⟨ba, F, rb, hF, sF⟩ := hk a
      obtain ⟨t, o, rfl, ht⟩ := hF
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      have someE : (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ↔ e = Bool.false := by
        constructor
        · rintro ⟨L, mL, x, hx⟩
          cases e
          · rfl
          · exact absurd ((sF (some x)).mpr ⟨L, mL, hx⟩ |> (fieldSem_mk.mp) |>.elim (fun h => by cases h.1)
              (fun ⟨y, ey, hy⟩ => by cases ey; exact hy)) (se.mp rfl x)
        · intro he
          subst he
          obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
            have := se.mpr fun y hy => h ⟨y, hy⟩; cases this
          obtain ⟨L, mL, hL⟩ := (sF (some x)).mp (fieldSem_mk.mpr (Or.inr ⟨x, rfl, hx⟩))
          exact ⟨L, mL, x, hL⟩
      have noneE : (∃ L ∈ lines, LongM den L a none) ↔ o = Bool.true := by
        rw [← sF, fieldSem_mk]; simp
      -- One step of the fold.
      let T₁ := if md ≠ "force" ∧ e = Bool.true then T else u
      let e₁ : List Term := if md ≠ "force" ∧ req = Bool.true ∧ (e = Bool.true ∨ (st = Bool.true ∧ o = Bool.true)) then
        [.tuple #[.atom "badkey", .atom a]] else []
      let f₁ : Bool := if md = "force" then Bool.true else if e then f else f || !(st && o)
      have hT₁ : E T₁ := by simp only [T₁]; split; exact hT; exact hu
      have step : (D (n + 4)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, .tuple #[.tuple #[.atom "constant", fld], .atom md], boolAtom req, boolAtom st, bd,
              .atom "true", boolAtom (decide (md = "force"))]) #[.atom a, .tuple #[T, B, Term.list Er, boolAtom f]] =
          .ok (.tuple #[T₁, ba.foldr Term.cons B, Term.list (e₁ ++ Er), boolAtom f₁]) := by
        have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", fld], .atom md]) bd (.atom "true") =
            .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) := rb
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb']
        rcases hmd with rfl | rfl | rfl <;> cases e <;> cases o <;> cases req <;> cases f <;> cases st <;>
          simp [T₁, e₁, f₁, re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom,
            Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«not/1», append_any, Term.list]
      obtain ⟨T', B', extra, f', r₁, hT', hx, hf⟩ := ih T₁ (ba.foldr Term.cons B) (e₁ ++ Er) f₁ hT₁
      refine ⟨T', B', extra ++ e₁, f', ?_, hT', fun x mx => ?_, ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        simp at step
        simp [step, r₁, List.append_assoc]
      · rcases List.mem_append.mp mx with mx | mx
        · exact hx x mx
        · simp only [e₁] at mx; split at mx
          · rw [List.mem_singleton] at mx; exact ⟨a, mx⟩
          · cases mx
      · rw [hf]
        have f₁E : f₁ = Bool.true ↔ f = Bool.true ∨ md = "force" ∨
            ((∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) := by
          rw [someE, noneE]
          simp only [f₁]
          by_cases hf : md = "force" <;> cases e <;> cases o <;> cases f <;> cases st <;> simp
        rw [f₁E]
        constructor
        · rintro ((h | h | h) | ⟨h₁, -⟩ | ⟨a', ma, h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h, by simp⟩)
          · exact Or.inr (Or.inr ⟨a, List.mem_cons_self, h⟩)
          · exact Or.inr (Or.inl ⟨h₁, by simp⟩)
          · exact Or.inr (Or.inr ⟨a', List.mem_cons_of_mem _ ma, h⟩)
        · rintro (h | ⟨h, -⟩ | ⟨a', ma, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · rcases List.mem_cons.mp ma with rfl | ma
            · exact Or.inl (Or.inr (Or.inr h))
            · exact Or.inr (Or.inr ⟨a', ma, h⟩)
  intro ks T B Er f hT
  obtain ⟨T', B', extra, f', r₁, hT', hx, hf⟩ := loop ks T B Er f hT
  refine ⟨T', B', extra, f', ?_, hT', hx, hf⟩
  rcases hmd with rfl | rfl | rfl
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, boolAtom]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      simpa [boolAtom] using r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa [boolAtom] using r₁

/-- The type `domain_key_to_descr/1` gives a kind of keys. -/
def domDescr (s : String) : Term :=
  match Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom s) with
  | .ok y => y
  | .error _ => .nil

/-- The error of a missing domain. -/
def bdErr : Term → Term
  | .atom s => .tuple #[.atom "baddomain", domDescr s]
  | _ => .nil

/-- `map_update_any_named_key?/2` finds a named key some map holds a value at. -/
theorem any_named_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ks : List String) :
    ∃ c : Bool, Elixir.Module.Types.Descr.«map_update_any_named_key?/2» (D (n + 4)) (Term.list lines)
      (Term.list (ks.map Term.atom)) = .ok (boolAtom c) ∧
      (c = Bool.true ↔ ∃ a ∈ ks, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) := by
  classical
  let res : Term → Bool := fun k => match k with
    | .atom a => decide (∃ L ∈ lines, ∃ x, LongM den L a (some x))
    | _ => Bool.false
  refine ⟨(ks.map Term.atom).any res, ?_, ?_⟩
  · simp only [Elixir.Module.Types.Descr.«map_update_any_named_key?/2»]
    refine any_list _ _ _ _ res _ fun x mx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp mx
    obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
    obtain ⟨ty, o, rfl, hty⟩ := hF
    obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hty
    have e : res (.atom a) = !b := by
      simp only [res]
      cases b
      · obtain ⟨x, hx⟩ : ∃ x, den ty x := Classical.byContradiction fun h => by
          have := sb.mpr fun y hy => h ⟨y, hy⟩; cases this
        obtain ⟨L, mL, hL⟩ := (sF (some x)).mp (fieldSem_mk.mpr (Or.inr ⟨x, rfl, hx⟩))
        simp only [Bool.not_false, decide_eq_true_eq]
        exact ⟨L, mL, x, hL⟩
      · simp only [Bool.not_true, decide_eq_false_iff_not]
        rintro ⟨L, mL, x, hL⟩
        have := (sF (some x)).mpr ⟨L, mL, hL⟩
        rw [fieldSem_mk] at this
        rcases this with ⟨h, -⟩ | ⟨y, ey, hy⟩
        · cases h
        · cases ey; exact sb.mp rfl _ hy
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_any_named_key?/2-fun-0-/1».pure, e]
    cases b <;> simp [Elixir.Module.Types.Descr.«-map_update_any_named_key?/2-fun-0-/2», rF, rb,
      Erlang.erlang.«not/1», boolAtom]
  · simp [res]

/-- `map_update_static_dnf/6` for a constant, asking for the old values: the errors are `badkey` errors and the
missing domains, which are those no line holds, and except when forcing, it finds a domain some line holds, a named
atom key some map holds a value at when updating atoms outside a set, or a named key every map holds a value at. -/
theorem dnf_flag (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md) (st : Bool)
    (bdd : Term) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk : List String)
    (neg : Term) (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hRk : R = [] ∨ rk = [])
    (hk : ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (boolAtom st) = .ok r) :
    ∃ (T Y : Term) (extra mis : List Term) (f : Bool), r = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧
      (∀ d, d ∈ mis ↔ ∃ s ∈ Ds, d = .atom s ∧ ¬∃ L ∈ lines, ∃ x, LineTag den L s x) ∧
      (md ≠ "force" → (f = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none))) ∧
      (md = "force" → (f = Bool.true ↔ Ds ≠ [] ∨ rk ≠ [] ∨ R ≠ [])) := by
  classical
  have m₀ : Erlang.erlang.«--/2» (Term.list (R.map Term.atom)) .nil = .ok (Term.list (R.map Term.atom)) := by
    simp [Erlang.erlang.«--/2», Term.properList?]
  have m₁ : Erlang.erlang.«--/2» (Term.list (R.map Term.atom)) (Term.list (rk.map Term.atom)) =
      .ok (Term.list (R.map Term.atom)) := by
    rcases hRk with rfl | rfl
    · have e0 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
          ([] : List Term) L = [] := fun L => by induction L <;> simp_all
      simp [Erlang.erlang.«--/2», e0, Term.properList?, Term.list]
    · simp [Erlang.erlang.«--/2», Term.properList?, Term.list]
  have m₂ : Erlang.erlang.«++/2» (Term.list (R.map Term.atom)) .nil = .ok (Term.list (R.map Term.atom)) := by
    simpa using append_list (R.map Term.atom) []
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  obtain ⟨c, hc, sc⟩ := any_named_sem ef (n := n) (by omega) lines hl (rk ++ R)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) #[] = .ok (boolAtom c) := by
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
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  -- The found flag of the named keys, from the domains.
  have fSem : ∀ f₀ f₂ f₃ : Bool, (f₀ = Bool.true ↔ f₁ = Bool.true) →
      (f₂ = Bool.true ↔ f₀ = Bool.true ∨ (md = "force" ∧ rk ≠ []) ∨
        ∃ a ∈ rk, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) →
      (f₃ = Bool.true ↔ f₂ = Bool.true ∨ (md = "force" ∧ R ≠ []) ∨
        ∃ a ∈ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) →
      md ≠ "force" → (f₃ = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) := by
    intro f₀ f₂ f₃ e₀ e₂ e₃ nf
    rw [e₃, e₂, e₀, fD₁, sc]
    simp only [nf, false_and, false_or, List.mem_append]
    constructor
    · rintro (((h | ⟨ha, a, ma, hh⟩) | ⟨a, ma, hh⟩) | ⟨a, ma, hh⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨ha, a, ma, hh⟩)
      · exact Or.inr (Or.inr ⟨a, Or.inl ma, hh⟩)
      · exact Or.inr (Or.inr ⟨a, Or.inr ma, hh⟩)
    · rintro (h | ⟨ha, a, ma, hh⟩ | ⟨a, ma | ma, hh⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨ha, a, ma, hh⟩))
      · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
      · exact Or.inr ⟨a, ma, hh⟩
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h
  simp only [splitT] at h
  have hmd₀ := hmd
  obtain ⟨md', hmd'⟩ : ∃ m, m = md := ⟨md, rfl⟩
  rcases hmd with rfl | rfl | rfl <;>
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃, mv,
      r₁'', r₂', rE', Lynx.Except.andAlso] at h
  all_goals
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨v44, h44, h⟩ := bind_ok h
    obtain ⟨v51, h51, h⟩ := bind_ok h
    -- The found flag the named keys start with.
    obtain ⟨f₀, rfl, ef₀⟩ : ∃ f₀ : Bool, v51 = boolAtom f₀ ∧ (md' ≠ "force" → (f₀ = Bool.true ↔ f₁ = Bool.true)) := by
      subst hmd'
      cases f₁ <;> simp [Lynx.Except.orElse, boolAtom] at hx <;> subst hx <;>
        (split at h51 <;> simp [Lynx.Except.orElse] at h51 <;> subst h51 <;>
          first
          | exact ⟨Bool.true, rfl, by simp⟩
          | exact ⟨Bool.false, rfl, by simp⟩
          | (split at h51 <;> simp at h51 <;> subst h51 <;>
              first | exact ⟨Bool.true, rfl, by simp⟩ | exact ⟨Bool.false, rfl, by simp⟩))
    have ff₀ : md' = "force" → (f₀ = Bool.true ↔ Ds ≠ [] ∨ f₁ = Bool.true) := by
      intro hf
      subst hmd'
      first
      | (simp at hf; done)
      | (clear h hk hcb hc r₁'' r₂' rE'
         cases f₁ <;> simp [Lynx.Except.orElse, boolAtom] at hx <;> subst hx <;>
           rcases Ds with _ | ⟨d, Ds⟩ <;> simp [Term.list, Lynx.Except.orElse] at h44 <;> subst h44 <;>
           cases f₀ <;> simp [boolAtom, Lynx.Except.orElse] at h51 ⊢)
    obtain ⟨X, hX, h⟩ := bind_ok h
    have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
      clear h
      simp only [bind, Except.bind, Except.tryWith] at hX
      repeat' split at hX
      all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
      all_goals done
    obtain ⟨B96, -, h⟩ := bind_ok h
    obtain ⟨r97, h97, h⟩ := bind_ok h
    obtain ⟨T', B', extra, f₂, e97, hT', hx₁, hf₂⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.true st
      (.atom "true") (fun a => hk Bool.true a) rk T₁ B96 (mis₁.map bdErr) f₀ hT₁
    have e₁ := h97.symm.trans e97
    cases e₁
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h
    obtain ⟨r5, h5, h⟩ := bind_ok h
    obtain ⟨T'', B'', extra', f₃, e5, -, hx₂, hf₃⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.false st
      (boolAtom bd) (fun a => hk bd a) R T' B' (extra ++ mis₁.map bdErr) f₂ hT'
    have e₂ := h5.symm.trans e5
    cases e₂
    obtain ⟨u, -, h⟩ := bind_ok h
    have fin : md' ≠ "force" → (f₃ = Bool.true ↔ (∃ s ∈ Ds, ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ∧ ∃ a ∈ rk ++ R, ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a ∈ rk ++ R, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧ (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none)) := by
      subst hmd'
      exact fun nf => fSem f₀ f₂ f₃ (ef₀ nf) hf₂ hf₃ nf
    have bk : ∀ e ∈ extra' ++ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a] := fun e me => by
      rcases List.mem_append.mp me with me | me
      · exact hx₂ e me
      · exact hx₁ e me
    have fin2 : md' = "force" → (f₃ = Bool.true ↔ Ds ≠ [] ∨ rk ≠ [] ∨ R ≠ []) := by
      intro hf
      have f₁D : f₁ = Bool.true → Ds ≠ [] := fun h1 => by
        rcases fD₁.mp h1 with ⟨s, ms, -⟩ | ⟨ms, -⟩ <;> exact List.ne_nil_of_mem ms
      rw [hf₃, hf₂, ff₀ hf]
      subst hmd'
      first
      | (simp at hf; done)
      | (constructor
         · rintro (((h0 | h1) | ⟨-, h2⟩ | ⟨a, ma, -⟩) | ⟨-, h3⟩ | ⟨a, ma, -⟩)
           · exact Or.inl h0
           · exact Or.inl (f₁D h1)
           · exact Or.inr (Or.inl h2)
           · exact Or.inr (Or.inl (List.ne_nil_of_mem ma))
           · exact Or.inr (Or.inr h3)
           · exact Or.inr (Or.inr (List.ne_nil_of_mem ma))
         · rintro (h0 | h2 | h3)
           · exact Or.inl (Or.inl (Or.inl h0))
           · exact Or.inl (Or.inr (Or.inl ⟨rfl, h2⟩))
           · exact Or.inr (Or.inl ⟨rfl, h3⟩))
    subst hmd'
    split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, extra' ++ extra, mis₁, f₃, by rw [List.append_assoc], bk, mD₁, fin, fin2⟩)

/-- `dnf_flag` on the lines of a map field: the missing domains other than atoms are the kinds no map holds, and with
no named atoms, except when forcing, it finds a key exactly when some map holds a value at a key of the split. -/
theorem dnf_flag_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String}
    {neg : Term} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (.atom "true") = .ok r) :
    ∃ (T Y : Term) (extra mis : List Term) (f : Bool), r = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, denMF E den b w = Bool.true ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, denMF E den b w = Bool.true ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split (den := den) ef fb (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_of fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  have hRk : R' = [] ∨ rk = [] := by
    cases R' with
    | nil => exact Or.inl rfl
    | cons r rs =>
      obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
      exact Or.inr (nr N eN)
  obtain ⟨T, Y, extra, mis, f, rfl, hx, hmis, hf, -⟩ := dnf_flag ef hn fld hmd Bool.true b lines hl rk neg Ds hDs R' rR hRk
    (hkL lines hl) r h
  have heldE : ∀ s ∈ Ds, s ≠ "atom" → ((∃ L ∈ lines, ∃ x, LineTag den L s x) ↔
      ∃ w, denMF E den b w = Bool.true ∧ HasKind w s) := fun s ms sa => by
    rw [← kind_held_ne ef hl (hDs s ms) sa]
    exact ⟨fun h => let ⟨u, hu, hk⟩ := h.2 sa; ⟨u, (sl u).mpr hu, hk⟩,
      fun ⟨u, hu, hk⟩ => ⟨fun e => absurd e sa, fun _ => ⟨u, (sl u).mp hu, hk⟩⟩⟩
  refine ⟨T, Y, extra, mis, f, rfl, hx, fun d md' => ?_, fun s ms sa => ?_, fun nf rk0 => ?_⟩
  · obtain ⟨s, ms, e, -⟩ := (hmis d).mp md'; exact ⟨s, ms, e⟩
  · rw [hmis, ← heldE s ms sa]
    constructor
    · rintro ⟨s', ms', e, h⟩; cases e; exact h
    · intro h; exact ⟨s, ms, rfl, h⟩
  · subst rk0
    rw [hf nf]
    have atomR : ∀ a ∈ R', "atom" ∈ Ds := fun a ma => by
      obtain ⟨s, -, N, eN, -⟩ := hR _ (List.mem_map_of_mem ma)
      obtain ⟨s', ms', e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, eN⟩)
      cases e; exact ms'
    have pe := fun x => pieces_sem ef lines hl sl ok hR swR x
    simp only [List.map_nil, List.nil_append, List.not_mem_nil, false_and, exists_false, false_or] at pe ⊢
    constructor
    · rintro (⟨s, ms, L, mL, x, hx'⟩ | ⟨-, a, ma, L, mL, x, hx'⟩ | ⟨a, ma, ⟨L, mL, x, hx'⟩, -⟩)
      · exact ⟨x, (pe x).mp (Or.inr ⟨s, List.mem_map_of_mem ms, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
    · rintro ⟨x, hw⟩
      rcases (pe x).mpr hw with ⟨a, ma, L, mL, hx'⟩ | ⟨s, ms, L, mL, hx'⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp ma
        injection e with e; subst e
        exact Or.inr (Or.inl ⟨atomR a' ma', a', ma', L, mL, x, hx'⟩)
      · obtain ⟨s', ms', e⟩ := List.mem_map.mp ms
        injection e with e; subst e
        exact Or.inl ⟨s', ms', L, mL, x, hx'⟩

/-- Whether an update finds a key, from the maps of a type: when forcing, whether the key type names an atom or holds a
kind; otherwise, without named atoms, whether some map holds a value at a key of the split, and with named atoms (and
no negated set), whether some map holds a key of a kind of the split, or holds a value at a named atom that, on static
types, every map holds. -/
def FoundS (M : MW V → Prop) (rk : List String) (neg : Term) (Ds : List String) (md : String) (st : Bool) : Prop :=
  (md = "force" ∧ (Ds ≠ [] ∨ rk ≠ [])) ∨
  (md ≠ "force" ∧ rk = [] ∧ ∃ x w, M w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x) ∨
  (md ≠ "force" ∧ rk ≠ [] ∧ ((∃ s ∈ Ds, ∃ w, M w ∧ HasKind w s) ∨
    ∃ a ∈ rk, (∃ w x, M w ∧ w (.atom a) = some x) ∧ (st = Bool.true → ∀ w, M w → w (.atom a) ≠ none)))

/-- `dnf_flag` on the lines of a map field, for any mode, static or not: the found flag is `FoundS` of its maps. -/
theorem dnf_found (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (st : Bool)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String}
    {neg : Term} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (boolAtom st) = .ok r) :
    ∃ (T Y : Term) (el : List Term) (f : Bool), r = .tuple #[T, Y, Term.list el, boolAtom f] ∧
      (f = Bool.true ↔ FoundS (fun u => denMF E den b u = Bool.true) rk neg Ds md st) := by
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split (den := den) ef fb (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_of fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  have hRk : R' = [] ∨ rk = [] := by
    cases R' with
    | nil => exact Or.inl rfl
    | cons r rs =>
      obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
      exact Or.inr (nr N eN)
  obtain ⟨T, Y, extra, mis, f, rfl, -, -, hf, hff⟩ := dnf_flag ef hn fld hmd st b lines hl rk neg Ds hDs R' rR hRk
    (hkL lines hl) r h
  refine ⟨T, Y, extra ++ mis.map bdErr, f, rfl, ?_⟩
  have atomR : ∀ a ∈ R', "atom" ∈ Ds := fun a ma => by
    obtain ⟨s, -, N, eN, -⟩ := hR _ (List.mem_map_of_mem ma)
    obtain ⟨s', ms', e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, eN⟩)
    cases e; exact ms'
  by_cases fo : md = "force"
  · rw [hff fo]
    simp only [FoundS, fo, ne_eq, not_true_eq_false, false_and, or_false, true_and]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨a, as⟩ := List.exists_mem_of_ne_nil R' h
        exact Or.inl (List.ne_nil_of_mem (atomR a as))
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rw [hf fo]
  by_cases rk0 : rk = []
  · subst rk0
    have pe := fun x => pieces_sem ef lines hl sl ok hR swR x
    simp only [FoundS, fo, false_and, false_or, ne_eq, not_false_eq_true, true_and, not_true_eq_false, and_false,
      or_false, List.map_nil, List.nil_append, List.not_mem_nil, exists_false] at pe ⊢
    constructor
    · rintro (⟨s, ms, L, mL, x, hx'⟩ | ⟨-, a, ma, L, mL, x, hx'⟩ | ⟨a, ma, ⟨L, mL, x, hx'⟩, -⟩)
      · exact ⟨x, (pe x).mp (Or.inr ⟨s, List.mem_map_of_mem ms, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
      · exact ⟨x, (pe x).mp (Or.inl ⟨a, List.mem_map_of_mem ma, L, mL, hx'⟩)⟩
    · rintro ⟨x, hw⟩
      rcases (pe x).mpr hw with ⟨a, ma, L, mL, hx'⟩ | ⟨s, ms, L, mL, hx'⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp ma
        injection e with e; subst e
        exact Or.inr (Or.inl ⟨atomR a' ma', a', ma', L, mL, x, hx'⟩)
      · obtain ⟨s', ms', e⟩ := List.mem_map.mp ms
        injection e with e; subst e
        exact Or.inl ⟨s', ms', L, mL, x, hx'⟩
  · -- Named atoms: no negated set, so no atoms outside it and no atom kind.
    have nn : neg = .atom "nil" := by
      rcases ok.hneg with h | ⟨N, h⟩
      · exact h
      · exact absurd (nr N h) rk0
    have R0 : R' = [] := by
      cases R' with
      | nil => rfl
      | cons r rs =>
        obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
        rw [nn] at eN; cases eN
    have na : "atom" ∉ Ds := fun ma => by
      obtain ⟨N, eN⟩ := ok.hatom.mp (List.mem_map_of_mem ma)
      rw [nn] at eN; cases eN
    subst R0
    have heldE : ∀ s ∈ Ds, ((∃ L ∈ lines, ∃ x, LineTag den L s x) ↔
        ∃ w, denMF E den b w = Bool.true ∧ HasKind w s) := fun s ms => by
      have sa : s ≠ "atom" := fun e => na (e ▸ ms)
      rw [← kind_held_ne ef hl (hDs s ms) sa]
      exact ⟨fun h => let ⟨u, hu, hk⟩ := h.2 sa; ⟨u, (sl u).mpr hu, hk⟩,
        fun ⟨u, hu, hk⟩ => ⟨fun e => absurd e sa, fun _ => ⟨u, (sl u).mp hu, hk⟩⟩⟩
    have lm := fun a o => longM_iff (E := E) (den := den) sl a o
    simp only [FoundS, fo, rk0, false_and, false_or, ne_eq, not_false_eq_true, true_and, List.append_nil, na,
      false_and, false_or] at lm ⊢
    constructor
    · rintro (⟨s, ms, h⟩ | ⟨a, ma, ⟨L, mL, x, hx'⟩, hn'⟩)
      · exact Or.inl ⟨s, ms, (heldE s ms).mp h⟩
      · obtain ⟨w, hw, wa⟩ := (lm a (some x)).mp ⟨L, mL, hx'⟩
        refine Or.inr ⟨a, ma, ⟨w, x, hw, wa⟩, fun hs w' hw' e => hn' hs ((lm a none).mpr ⟨w', hw', e⟩)⟩
    · rintro (⟨s, ms, w, hw, hk⟩ | ⟨a, ma, ⟨w, x, hw, wa⟩, hn'⟩)
      · obtain ⟨L, mL, x, hx'⟩ := (heldE s ms).mpr ⟨w, hw, hk⟩
        exact Or.inl ⟨s, ms, L, mL, x, hx'⟩
      · obtain ⟨L, mL, hL⟩ := (lm a (some x)).mpr ⟨w, hw, wa⟩
        refine Or.inr ⟨a, ma, ⟨L, mL, x, hL⟩, fun hs ⟨L', mL', h'⟩ => ?_⟩
        obtain ⟨w', hw', e⟩ := (lm a none).mp ⟨L', mL', h'⟩
        exact hn' hs w' hw' e

/-- `map_update_static/5` for a constant at a split of static keys, asking for the old values: `:badmap`, or the
errors and found flag `dnf_flag_sem` gives. -/
theorem flag_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (res : Term)
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") = .ok res) :
    res = .atom "badmap" ∨ ∃ (T Y : Term) (extra mis : List Term) (f : Bool),
      res = .tuple #[T, Y, Term.list (extra ++ mis.map bdErr), boolAtom f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, denMF E den b w = Bool.true ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, denMF E den b w = Bool.true ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
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
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
            (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      rw [unf] at run
      obtain ⟨T, Y, extra, mis, f, e, hx, hm, hmk, hf⟩ := dnf_flag_sem ef hn fld hmd hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, extra, mis, f, e, ⟨w₀, (sem w₀).mpr h₀⟩, hx, hm, hmk, hf⟩
    · left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom] at run
      exact run.symm
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
      left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
    | cons L rest =>
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest))
            (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      rw [unf] at run
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      obtain ⟨T, Y, extra, mis, f, e, hx, hm, hmk, hf⟩ := dnf_flag_sem ef hn fld hmd hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, extra, mis, f, e, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hx, hm, hmk, hf⟩




/-- `map_update_static/5` for a constant at a split of static keys, asking for the old values: `:badmap`, or the
found flag `dnf_found` gives, static or not. -/
theorem static_found (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md) (st : Bool)
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a,
      ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (res : Term)
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (boolAtom st) = .ok res) :
    res = .atom "badmap" ∨ ∃ (T Y : Term) (er : List Term) (f : Bool), res = .tuple #[T, Y, Term.list er, boolAtom f] ∧
      (∃ w, denMF E den b w = Bool.true) ∧ (f = Bool.true ↔ FoundS (fun u => denMF E den b u = Bool.true) rk neg Ds md st) := by
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
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (boolAtom st) =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
            (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (boolAtom st) := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      rw [unf] at run
      obtain ⟨T, Y, er, f, e, hf⟩ := dnf_found ef hn fld hmd st hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, er, f, e, ⟨w₀, (sem w₀).mpr h₀⟩, hf⟩
    · left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom] at run
      exact run.symm
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
      left
      unfold Elixir.Module.Types.Descr.«map_update_static/5» at run
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, Term.list] at run; exact run.symm
    | cons L rest =>
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (boolAtom st) =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest))
            (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (boolAtom st) := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      rw [unf] at run
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      obtain ⟨T, Y, er, f, e, hf⟩ := dnf_found ef hn fld hmd st hkL fb _ hl inB ok nr res run
      exact Or.inr ⟨T, Y, er, f, e, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hf⟩



end

section
variable {t : Term} {n : Nat}

/-- `map_update/5` for a constant at a static key type, asking for the old values, on static types of the next
level: `:badmap`, or the errors and found flag `flag_static` gives, an error exactly when nothing is found. -/
theorem flag_update {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key v : Term} {rk Ds : List String}
    {neg : Term} {m : Nat} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (fld : Term) {md : String} (hmd : Mode md) (hm : (level t n).K + 26 ≤ m)
    (hupd : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
        (.atom "true"))
    (hkL : ∀ k, k + 6 = m → ∀ lines : List Term, (∀ L ∈ lines, MLine (level t n).E L ∧ ∃ w, InMLine (level t n).den L w) →
      ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (k + 5))
        (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue (level t n).E F ∧
        ∀ o, FieldSem (level t n).den F o ↔ ∃ L ∈ lines, LongM (level t n).den L a o)
    {r : Term} (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") = .ok r) :
    r = .atom "badmap" ∨ ∃ (er : Term) (extra mis : List Term) (f : Bool), MOnly t n X ∧
      er = Term.list (extra ++ mis.map bdErr) ∧
      ((f = Bool.false ∧ r = .tuple #[.atom "error", er]) ∨ (f = Bool.true ∧ ∃ T Y, r = .tuple #[T, Y, er])) ∧
      (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) ∧ (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, MT t n X w ∧ HasKind w s)) ∧
      (md ≠ "force" → rk = [] → (f = Bool.true ↔ ∃ x w, MT t n X w ∧
        ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rw [hupd] at run
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», sX.static] at run
  cases hb : mapLookup X (.atom "map") with
  | none =>
    left
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
    exact run.symm
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 6) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 6)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      cases hs : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 6)) (.map X)
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true")
          (.atom "true") with
      | error e => simp [key, mo, hs, Lynx.Except.andAlso] at run
      | ok res =>
        rcases flag_static (level t n).ef (n := k) (by omega) fld hmd (hkL k rfl) ok nr hb fb res hs with
          rfl | ⟨T, Y, extra, mis, f, rfl, ⟨w₀, hw₀⟩, hx, hm', hmk, hf⟩
        · left
          simp [key, mo, hs, Lynx.Except.andAlso,
            Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
            Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
          exact run.symm
        · right
          refine ⟨_, extra, mis, f, only.mpr ⟨restE, w₀, hw₀⟩, rfl, ?_, hx, hm', fun s ms sa => by rw [hmk s ms sa]; simp only [mt],
            fun nf rk0 => by rw [hf nf rk0]; simp only [mt]⟩
          cases f
          · left; refine ⟨rfl, ?_⟩
            simp [key, mo, hs, Lynx.Except.andAlso, boolAtom, Lynx.Term.isMember] at run; exact run.symm
          · right; refine ⟨rfl, T, Y, ?_⟩
            simp [key, mo, hs, Lynx.Except.andAlso, boolAtom, Lynx.Term.isMember] at run; exact run.symm
    · rw [bp_false.mpr restE] at mo
      left
      simp [key, mo, Lynx.Except.andAlso, boolAtom,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
      exact run.symm

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_named_key/5` for `:keep` and `:reject` of a value with values gives the maps and the old field. -/
theorem hk_val (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  cases bd
  · obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
    exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, sF⟩
  · obtain ⟨ba, F, rb, -, hF, sF, -⟩ := keep_lines ef hn a hv vne keep lines hl (.atom "true")
    exact ⟨ba, F, rb, hF, sF⟩

/-- `map_update_named_key/5` deleting a key gives the maps and the old field. -/
theorem hk_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨ba, F, rb, -, -, -⟩ := del_key_sem ef hn lines hl hmd a bd
  obtain ⟨bdds, F', e, hF, sF⟩ := del_key ef hn lines hl md hmd bd a _ rb
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨-, rfl⟩ := e
  exact ⟨ba, F, rb, hF, sF⟩

end

section
variable {t : Term} {n : Nat}

/-- A static key type without named atoms splits into no required atoms. -/
theorem unnamed_rs {key : Term} {rs : List Term} {neg : Term} {ds : List Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) (sk : ∀ κ, SplitKey rs neg ds κ ↔ KeyPt t n key κ) (A : List String)
    (h : (∀ s, ¬KeyPt t n key (.atom s)) ∨ (∀ s, KeyPt t n key (.atom s)) ∨
      ∀ s, ¬KeyPt t n key (.atom s) → s ∈ A) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    exfalso
    obtain ⟨a, rfl⟩ := ok.hrs r List.mem_cons_self
    have hneg : neg = .atom "nil" := by
      rcases ok.hneg with e | ⟨N, e⟩
      · exact e
      · cases nr N e
    subst hneg
    have strs : ∀ s, KeyPt t n key (.atom s) ↔ .atom s ∈ Term.atom a :: rest := fun s => by
      rw [← sk]; simp [SplitKey]
    obtain ⟨c, hc⟩ := fresh_str (A ++ ((Term.atom a :: rest).filterMap fun r => match r with
      | .atom s => some s
      | _ => none))
    have nc : ¬KeyPt t n key (.atom c) := fun hk => hc (List.mem_append_right _ (List.mem_filterMap.mpr
      ⟨_, (strs c).mp hk, rfl⟩))
    rcases h with h | h | h
    · exact h a ((strs a).mpr List.mem_cons_self)
    · exact nc (h c)
    · exact hc (List.mem_append_left _ (h c nc))

end

section
variable {t : Term} {n : Nat}

/-- `atom/1` on a non-empty list of atoms: the type of those atoms. -/
theorem atomsY (A : List String) (hA : A ≠ []) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ Y, Elixir.Module.Types.Descr.«atom/1» (Term.list (A.map Term.atom)) = .ok (.map Y) ∧ DE (level t n).E (.map Y) ∧
      ∀ s, denD (.map Y) (aPt (t := t) (n := n) (.atom s)) ↔ s ∈ A := by
  have ha : ∀ a ∈ A.map Term.atom, ∃ s, a = .atom s := fun a ma => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp ma; exact ⟨s, rfl⟩
  obtain ⟨Y, rY, hY⟩ := key_type_run (t := t) (n := n) (A.map Term.atom) [] ha (by simp) (m := m) hm
  refine ⟨Y, ?_, hY.de, fun s => ?_⟩
  · cases A with
    | nil => exact absurd rfl hA
    | cons a A =>
      have := rY
      simp only [Elixir.STTDescrProofsTest.«key_type/2», Term.list, List.map] at this
      simp only [Term.list, List.map]
      cases hr : Elixir.Module.Types.Descr.«atom/1» (Term.cons (.atom a) (Term.list (A.map Term.atom))) with
      | error e => simp [hr] at this
      | ok r => simp [hr, Elixir.STTDescrProofsTest.«kinds_type/2»] at this; rw [this]
  · rw [hY.atoms]; simp

/-- `unnamed_keys?/2` on a static key type: the atoms are a list, and the key type holds no atom, every atom, or every
atom but those of the list. -/
theorem unnamed_ok {key atoms : Term} (dk : DE (level t n).E key) {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : Elixir.STTDescrProofsTest.«unnamed_keys?/2» (D m) key atoms = .ok (.atom "true")) :
    ∃ A : List String, atoms = Term.list (A.map Term.atom) ∧ ((∀ s, ¬KeyPt t n key (.atom s)) ∨
      (∀ s, KeyPt t n key (.atom s)) ∨ ∀ s, ¬KeyPt t n key (.atom s) → s ∈ A) := by
  simp only [Elixir.STTDescrProofsTest.«unnamed_keys?/2», Lynx.Except.andAlso_eq_true] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨as, ks, rfl, -, ha, -⟩ := keys_ok hk
  obtain ⟨A, rfl⟩ := atoms_of ha
  refine ⟨A, rfl, ?_⟩
  have kA := kind_atom (t := t) (n := n)
  simp only [Elixir.Module.Types.Descr.«atom/0», pure, Except.pure, Lynx.Except.ok_bind] at h
  rw [next_disj dk kA.de hm] at h
  by_cases dj : ∀ v : PN t n, denD key v → denD (.map [(.atom "atom", .tuple #[.atom "negation", .map []])]) v → False
  · exact Or.inl fun s hs => dj _ hs (kA.atoms rfl _)
  rw [bp_false.mpr dj] at h
  rw [next_sub kA.de dk hm] at h
  by_cases sb : SubN t n (.map [(.atom "atom", .tuple #[.atom "negation", .map []])]) key
  · exact Or.inr (Or.inl fun s => sb _ (kA.atoms rfl _))
  rw [bp_false.mpr sb] at h
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte, Lynx.Except.orElse_false] at h
  cases A with
  | nil => simp [Erlang.erlang.«/=/2», Term.list] at h
  | cons a A' =>
    obtain ⟨c, dc, rc, sc⟩ := (ef_next t n).opt_diff [] kA.de dk (m := m) hm
    obtain ⟨Y, rY, dY, sY⟩ := atomsY (t := t) (n := n) (a :: A') (by simp) hm
    have ne : Erlang.erlang.«/=/2» (Term.list ((a :: A').map Term.atom)) .nil = .ok (.atom "true") := by
      simp [Erlang.erlang.«/=/2», Term.list]
    rw [ne, Lynx.Except.andAlso_true] at h
    simp only [Elixir.Module.Types.Descr.«opt_difference/2», rc, rY, Lynx.Except.ok_bind] at h
    rw [next_sub dc dY hm] at h
    by_cases sub : SubN t n c (.map Y)
    · exact Or.inr (Or.inr fun s hs => (sY s).mp (sub _ ((sc _).mpr ⟨kA.atoms rfl _, hs⟩)))
    · rw [bp_false.mpr sub] at h; simp [boolAtom] at h

end


section
variable {t : Term} {n : Nat}

/-- The literal of the list domain holds the points of its two fields. -/
theorem listLit_den (v : PN t n) :
    denD (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) v ↔
      denD (.map [(.atom "bitmap", .integer 4)]) v ∨
        denD (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) v := by
  rw [denD_field, denD_field, denD_field]
  simp only [lookup_cons_atom]
  by_cases hb : "bitmap" = v.1.1 <;> by_cases hl : "list" = v.1.1 <;> simp [hb, hl, mapLookup] <;>
    exact absurd (hb.trans hl.symm) (by decide)

/-- The domain type of a kind other than atoms, as `kind_type/1` and `domain_key_to_descr/1` give it: the points of
that kind. -/
theorem kind_exact {k : String} (hk : k ∈ domainKinds) (ka : k ≠ "atom") {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom k) = .ok (.map T) ∧ DE (level t n).E (.map T) ∧
      (∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) ∧ DE (level t n).E (domDescr k) ∧
      ∀ v : PN t n, denD (domDescr k) v ↔ ptKind v = k := by
  obtain ⟨T, rT, kT⟩ := kind_run (t := t) (n := n) hk hm
  have dD := (dkdT_run (t := t) (n := n) hk).2
  have eD : domDescr k = dkdT k := by
    have r := (dkdT_run (t := t) (n := n) hk).1
    unfold domDescr; rw [r]
  have pT : ∀ v : PN t n, denD (.map T) v → ptKind v = k := fun v hv => by
    rcases kT.pts v hv with ⟨e, -⟩ | ⟨-, h⟩
    · exact absurd e ka
    · exact h
  by_cases kl : k = "list"
  · subst kl
    have eL : dkdT "list" = .map [(.atom "bitmap", .integer 4),
        (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])] := rfl
    have b2 := kind_bit (t := t) (n := n) 2 (by omega)
    simp only [show ((2 ^ 2 : Nat) : Int) = 4 from rfl] at b2
    have dl : DE (level t n).E (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) :=
      single_de (by simp [names]) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr
        ⟨46675407, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩))))
    obtain ⟨U, rU, dU, sU⟩ := union_map b2.de dl hm
    have eU : T = U := by
      have r2 : Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom "list") = .ok (.map U) := by
        simp [Elixir.STTDescrProofsTest.«kind_type/1», Elixir.Module.Types.Descr.«empty_list/0»,
          Elixir.Module.Types.Descr.«term/0», non_empty_list_top, rU]
      have := rT.symm.trans r2
      simp only [Except.ok.injEq, Term.map.injEq] at this
      exact this
    subst eU
    have same : ∀ v : PN t n, denD (.map T) v ↔ denD (dkdT "list") v := fun v => by
      rw [sU, eL, listLit_den]
    have full : ∀ v : PN t n, ptKind v = "list" → denD (dkdT "list") v := fun v h => dD.kinds (by simp) v h
    refine ⟨T, rT, dU, fun v => ⟨pT v, fun h => (same v).mpr (full v h)⟩, by rw [eD]; exact dD.de, fun v => ?_⟩
    rw [eD]
    exact ⟨fun h => pT v ((same v).mpr h), full v⟩
  · have eT : dkdT k = .map T := by
      have r2 := (dkdT_run (t := t) (n := n) hk).1
      simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl ka
        | exact absurd rfl kl
        | (simp only [Elixir.STTDescrProofsTest.«kind_type/1»] at rT
           simp only [Elixir.Module.Types.Descr.«domain_key_to_descr/1»] at r2
           rw [rT] at r2
           exact (Except.ok.inj r2).symm)
    have full : ∀ v : PN t n, ptKind v = k → denD (.map T) v := fun v h => by rw [← eT]; exact dD.kinds ka v h
    refine ⟨T, rT, kT.de, fun v => ⟨pT v, full v⟩, by rw [eD, eT]; exact kT.de, fun v => ?_⟩
    rw [eD, eT]
    exact ⟨pT v, full v⟩

end


section
variable {t : Term} {n : Nat}

/-- The error type of a missing domain: the points of its kind, with one. -/
theorem domDescr_kind {s : String} (hs : s ∈ domainKinds) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    DE (level t n).E (domDescr s) ∧ (∃ v : PN t n, denD (domDescr s) v ∧ ptKind v = s) ∧
      ∀ v : PN t n, denD (domDescr s) v → ptKind v = s := by
  by_cases sa : s = "atom"
  · subst sa
    have e : domDescr "atom" = .map [(.atom "atom", .tuple #[.atom "negation", .map []])] := by
      simp [domDescr, Elixir.Module.Types.Descr.«domain_key_to_descr/1», Elixir.Module.Types.Descr.«atom/0»]
    have kA := kind_atom (t := t) (n := n)
    rw [e]
    refine ⟨kA.de, ⟨aPt (.atom "a"), kA.atoms rfl _, by simp [ptKind, aPt]⟩, fun v hv => ?_⟩
    rcases kA.pts v hv with ⟨-, h⟩ | ⟨h, -⟩
    · simp [ptKind, h]
    · exact absurd (((denD_single _ _ v).mp hv).1) h
  · obtain ⟨T, rT, dT, sT, dD, sD⟩ := kind_exact (t := t) (n := n) hs sa hm
    obtain ⟨T', rT', kT⟩ := kind_run (t := t) (n := n) hs hm
    obtain rfl : T' = T := by
      have := rT'.symm.trans rT
      simp only [Except.ok.injEq, Term.map.injEq] at this
      exact this
    obtain ⟨v, hv, pv⟩ := kT.wit sa
    exact ⟨dD, ⟨v, (sD v).mpr pv, pv⟩, fun v hv => (sD v).mp hv⟩

/-- `has_baddomain?/2` skips `badkey` errors. -/
theorem has_bd_keys (m : Nat) (T : Term) : ∀ (extra rest : List Term),
    (∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a]) →
    Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list (extra ++ rest)) T =
      Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list rest) T
  | [], rest, _ => rfl
  | e :: extra, rest, h => by
    obtain ⟨a, rfl⟩ := h e List.mem_cons_self
    rw [← has_bd_keys m T extra rest fun e me => h e (List.mem_cons_of_mem _ me)]
    simp [Term.list, Elixir.STTDescrProofsTest.«has_baddomain?/2»]

/-- `has_baddomain?/2` over the errors of missing domains finds the domain of a kind exactly when it is missing. -/
theorem has_bd_mis {k : String} (hk : k ∈ domainKinds) (ka : k ≠ "atom") {m : Nat} (hm : (level t n).K + 23 ≤ m)
    {T : List (Term × Term)} (dT : DE (level t n).E (.map T)) (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) :
    ∀ mis : List Term, (∀ d ∈ mis, ∃ s ∈ domainKinds, d = .atom s) →
      ∃ b : Bool, Elixir.STTDescrProofsTest.«has_baddomain?/2» (D m) (Term.list (mis.map bdErr)) (.map T) =
        .ok (boolAtom b) ∧ (b = Bool.true ↔ .atom k ∈ mis)
  | [], _ => ⟨Bool.false, by simp [Term.list, Elixir.STTDescrProofsTest.«has_baddomain?/2», boolAtom], by simp⟩
  | d :: mis, h => by
    obtain ⟨b, rb, sb⟩ := has_bd_mis hk ka hm dT sT mis fun d md => h d (List.mem_cons_of_mem _ md)
    obtain ⟨s, hs, rfl⟩ := h d List.mem_cons_self
    obtain ⟨dD, ⟨w, hw, pw⟩, sD⟩ := domDescr_kind (t := t) (n := n) hs hm
    by_cases e : s = k
    · subst e
      have s₁ : SubN t n (domDescr s) (.map T) := fun v hv => (sT v).mpr (sD v hv)
      obtain ⟨-, -, -, -, -, sD'⟩ := kind_exact (t := t) (n := n) hk ka hm
      have s₂ : SubN t n (.map T) (domDescr s) := fun v hv => (sD' v).mpr ((sT v).mp hv)
      refine ⟨Bool.true, ?_, by simp⟩
      simp [Term.list, bdErr, Elixir.STTDescrProofsTest.«has_baddomain?/2», next_sub dD dT hm, bp_true.mpr s₁,
        next_sub dT dD hm, bp_true.mpr s₂, boolAtom]
    · have s₁ : ¬SubN t n (domDescr s) (.map T) := fun h' => e (pw.symm.trans ((sT w).mp (h' w hw)))
      refine ⟨b, ?_, ?_⟩
      · simp [Term.list, bdErr, Elixir.STTDescrProofsTest.«has_baddomain?/2», next_sub dD dT hm, bp_false.mpr s₁,
          boolAtom] at rb ⊢
        exact rb
      · rw [sb]; simp [Ne.symm e]

end


section
variable {t : Term} {n : Nat}

/-- A static type of points of a kind other than atoms splits into that kind. -/
theorem kind_keys {k : String} (ka : k ≠ "atom") {T : List (Term × Term)} (dT : DE (level t n).E (.map T))
    (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) (wT : ∃ v : PN t n, ptKind v = k) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map T) = .ok (splitT rs neg ds) ∧
      SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ ↔ ∃ k' i, κ = .dom k' i ∧ domKind k' = k := by
  have noAtom : ∀ q, ¬denD (.map T) (aPt (t := t) (n := n) q) := fun q h => by
    have := (sT _).mp h
    simp [ptKind, aPt] at this
    exact ka this.symm
  obtain ⟨rs, neg, ds, rk, ok, -, -, sk⟩ := key_split_any (t := t) (n := n) dT
    (fun Y e S hS q hq => by
      cases e
      exact absurd ((denD_aPt q).mpr (by rw [hS]; simpa [amemV] using hq)) (noAtom q))
    (fun Y e S hS => by
      cases e
      exfalso
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      exact noAtom (.atom c) ((denD_aPt _).mpr (by rw [hS]; simp [amemV, lookup_fresh' hc])))
    hm
  refine ⟨rs, neg, ds, rk, ok, fun κ => ?_⟩
  rw [sk]
  cases κ with
  | atom s => simp only [KeyPt, reduceCtorEq, false_and, exists_false, iff_false]; exact noAtom _
  | dom k' i =>
    simp only [KeyPt, MKey.dom.injEq]
    constructor
    · rintro ⟨v, hv, pv⟩; exact ⟨k', i, ⟨rfl, rfl⟩, pv ▸ ((sT v).mp hv)⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, e⟩
      obtain ⟨v, pv⟩ := wT
      exact ⟨v, (sT v).mpr pv, pv.trans e.symm⟩

/-- `map_get/2` at the type of a kind other than atoms finds nothing exactly when no map holds a key of that kind. -/
theorem get_kind {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) (only : MOnly t (n + 1) X)
    {k : String} (ka : k ≠ "atom") {T : List (Term × Term)} (dT : DE (level t n).E (.map T))
    (sT : ∀ v : PN t n, denD (.map T) v ↔ ptKind v = k) (wT : ∃ v : PN t n, ptKind v = k) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m) :
    ∃ (r g : Term) (b : Bool), Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) (.map T) = .ok r ∧
      Elixir.STTDescrProofsTest.«got/1» r = .ok g ∧ Elixir.Module.Types.Descr.«empty?/1» (D m) g = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ¬∃ w, MT t (n + 1) X w ∧ HasKind w k) := by
  have hK : (level t (n + 1)).K = (level t n).K + 24 := by rw [level_K, level_K]; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨rs, neg, ds, rk, ok, sk⟩ := kind_keys ka dT sT wT (m := m') (by omega)
  have ef := (level t (n + 1)).ef
  obtain ⟨res, run, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, ⟨x₀, hx₀⟩, sT₀⟩⟩ :=
    get_map (t := t) (n := n + 1) hX ok (m := m' + 1) (by omega) rk
  · exact absurd only nX
  · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := m' + 1) (by omega) ef.none
    have b1 : b = Bool.true := sb.mpr fun x hx => ef.den_none x hx
    subst b1
    refine ⟨_, _, Bool.true, run, by simp [Elixir.STTDescrProofsTest.«got/1», Elixir.Module.Types.Descr.«none/0»],
      rb, ?_⟩
    constructor
    · rintro - ⟨w, hw, k', i, ek, hi⟩
      exact hi (eX w hw _ ((sk _).mpr ⟨k', i, rfl, ek⟩))
    · intro _; rfl
  · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := m' + 1) (by omega) hT₀
    have b0 : b = Bool.false := by
      cases b
      · rfl
      · exact absurd hx₀ (sb.mp rfl x₀)
    subst b0
    refine ⟨_, _, Bool.false, run, by simp [Elixir.STTDescrProofsTest.«got/1», pure, Except.pure], rb, ?_⟩
    obtain ⟨w, hw, κ, hκ, e⟩ := (sT₀ x₀).mp hx₀
    obtain ⟨k', i, rfl, ek⟩ := (sk _).mp hκ
    exact ⟨fun h => (by cases h), fun h => absurd ⟨w, hw, k', i, ek, by rw [e]; simp⟩ h⟩

/-- `baddomains?/4` holds on the errors of an update, as `flag_update` gives them, over kinds other than atoms. -/
theorem bd_ok {X : List (Term × Term)} (hX : DE (level t (n + 1)).E (.map X)) (only : MOnly t (n + 1) X)
    {key : Term} (dk : DE (level t n).E key) {rs : List Term} {neg : Term} {Ds : List String}
    (skey : ∀ κ, SplitKey rs neg (Ds.map Term.atom) κ ↔ KeyPt t n key κ) (hDs : ∀ s ∈ Ds, s ∈ domainKinds)
    {extra mis : List Term} (hx : ∀ e ∈ extra, ∃ a, e = .tuple #[.atom "badkey", .atom a])
    (hmisD : ∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s)
    (hmk : ∀ s ∈ Ds, s ≠ "atom" → (.atom s ∈ mis ↔ ¬∃ w, MT t (n + 1) X w ∧ HasKind w s))
    {m : Nat} (hm : (level t (n + 1)).K + 26 ≤ m) :
    ∀ L : List String, (∀ k ∈ L, k ∈ domainKinds ∧ k ≠ "atom") →
      Elixir.STTDescrProofsTest.«baddomains?/4» (D m) (.map X) key (Term.list (extra ++ mis.map bdErr))
        (Term.list (L.map Term.atom)) = .ok (.atom "true")
  | [], _ => by simp [Term.list, Elixir.STTDescrProofsTest.«baddomains?/4»]
  | k :: L, hL => by
    have hK : (level t (n + 1)).K = (level t n).K + 24 := by rw [level_K, level_K]; omega
    obtain ⟨hk, ka⟩ := hL k List.mem_cons_self
    have ih := bd_ok hX only dk skey hDs hx hmisD hmk hm L fun k' mk => hL k' (List.mem_cons_of_mem _ mk)
    obtain ⟨T, rT, dT, sT, -, -⟩ := kind_exact (t := t) (n := n) hk ka (m := m) (by omega)
    obtain ⟨-, ⟨w₀, -, pw₀⟩, -⟩ := domDescr_kind (t := t) (n := n) hk (m := m) (by omega)
    obtain ⟨r, g, b₂, rg, gg, eg, sb₂⟩ := get_kind hX only ka dT sT ⟨w₀, pw₀⟩ hm
    obtain ⟨b₁, rb₁, sb₁⟩ := has_bd_mis (t := t) (n := n) hk ka (m := m) (by omega) dT sT mis fun d md => by
      obtain ⟨s, ms, rfl⟩ := hmisD d md; exact ⟨s, hDs s ms, rfl⟩
    rw [← has_bd_keys m (.map T) extra (mis.map bdErr) hx] at rb₁
    simp only [Term.list, List.map] at ih ⊢
    rw [Elixir.STTDescrProofsTest.«baddomains?/4».eq_def]
    simp only [rT, Lynx.Except.ok_bind, next_disj (m := m) dT dk (by omega)]
    by_cases dj : ∀ v : PN t n, denD (.map T) v → denD key v → False
    · rw [bp_true.mpr dj]; simp [boolAtom, ih]
    · -- The kind is a domain of the key type.
      obtain ⟨v, hvT, hvk⟩ : ∃ v : PN t n, denD (.map T) v ∧ denD key v := Classical.byContradiction fun h =>
        dj fun v a b => h ⟨v, a, b⟩
      obtain ⟨k', ek⟩ := domKind_of hk ka
      have kD : k ∈ Ds := by
        have := (skey (.dom k' 0)).mpr ⟨v, hvk, by rw [(sT v).mp hvT, ek]⟩
        simp only [SplitKey, ek, List.mem_map, Term.atom.injEq, exists_eq_right] at this
        exact this
      have eb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> first | rfl | (exfalso; simp_all)
      subst eb
      rw [bp_false.mpr dj]
      simp [boolAtom, rb₁, rg, gg, eg, Erlang.erlang.«==/2», ih]

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_named_key/5` forcing a value gives the maps and the old field. -/
theorem hk_force (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool) (a : String) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
        (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, sF⟩
  · obtain ⟨ba, rba, -, -⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
    exact ⟨ba, F, by simpa [boolAtom] using rba Bool.true F fun _ => rF, hF, sF⟩

end

end Elixir.STTDescrProofsTest.Nest

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
      i ≤ List.length w := by
  obtain ⟨k, run, key⟩ := leaf_new_key "open" (Or.inl rfl) (List.replicate i (.atom "term"))
  refine ⟨k, ?_, fused_de (Or.inl rfl) (fun e me => by rw [List.eq_of_mem_replicate me]; exact (level t n).ef.term) key,
    fun v hv => ?_, tt_open i k⟩
  · have ge : (Ord.compare (i : Int) 0).isGE = Bool.true := by
      rw [Ordering.isGE_iff_ne_lt]; intro h; rw [Int.compare_eq_lt] at h; omega
    simp [Elixir.Module.Types.Descr.«tuple_of_size_at_least/1», Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2»,
      dup_nat, Elixir.Module.Types.Descr.«tuple_new/2», run, Lynx.Except.andAlso, ge]
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
      simp [getMapKeys_single, hb]
    · simp only [TT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
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
    List.filter (fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (.atom "dynamic") entry.fst = .eq)) X =
      rmDyn X := rfl

theorem filter_t (Y : List (Term × Term)) :
    List.filter (fun entry => !decide (compareExact ((Term.atom "tuple").fuel entry.fst) (.atom "tuple") entry.fst = .eq)) Y =
      rmT Y := rfl

theorem filter_tdyn (X : List (Term × Term)) :
    List.filter (fun a => !decide (compareExact ((Term.atom "tuple").fuel a.fst) (.atom "tuple") a.fst = .eq) &&
      !decide (compareExact ((Term.atom "dynamic").fuel a.fst) (.atom "dynamic") a.fst = .eq)) X = rmT (rmDyn X) := by
  simp [rmT, rmDyn, List.filter_filter, Bool.and_comm]

/-- The static size check of a static type: when it holds, every tuple is long enough. -/
theorem size_check {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S) (.integer i)) = .ok (boolAtom sz) ∧
      (sz = Bool.true → ∀ w, TT t n S w → i ≤ List.length w) := by
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
      (∀ w, TT t n (rmDyn X) w → i ≤ List.length w) ∧
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
  simp only [Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2», equalExact_eq_decide] at run
  simp only [filter_dyn, filter_t, rkd, rto, rsz, Lynx.Except.ok_bind] at run
  -- Failed checks give an atom.
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    cases kd <;> cases sz <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] at run <;>
      subst run <;> simp
  rw [bp_true.mpr to] at run
  cases sz
  · cases kd <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] at run <;>
      subst run <;> simp
  cases kd
  · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] at run
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
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, Lynx.Except.ok_bind, equal_eq_decide] at run
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2] at run
    simp [Lynx.Term.isMember, Term.true] at run
    subst run; simp
  have eR : R' = r := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
    · exact absurd ⟨ec, es⟩ both
    all_goals
      first
      | rw [bp_true.mpr ec, bp_false.mpr es] at run
      | rw [bp_false.mpr ec, bp_true.mpr es] at run
      | rw [bp_false.mpr ec, bp_false.mpr es] at run
      simp [Lynx.Term.isMember, Term.true] at run
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
      (∀ w, TT t n (rmDyn X) w → i ≤ List.length w) ∧
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
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb, equalExact_eq_decide]
      rw [show (List.filter (fun entry => !decide (compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst = .eq)) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 3) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    -- The size check.
    obtain ⟨sz, rsz, ssz⟩ : ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i)) = .ok (boolAtom sz) ∧
        (sz = Bool.true → ∀ w, TT t n X w → i ≤ List.length w) := by
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
      (∀ w, TT t n (rmDyn X) w → i ≤ List.length w) ∧
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
    · simp [Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.orElse] at run
    · simp [Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.orElse] at run
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
  ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ List.length v₁ = i ∧ P (v₁ ++ y :: v₂)

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
    (long : ∀ w, TT t n X w → i < List.length w) {m : Nat} (hm : (level t n).K + 4 ≤ m) :
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
    · simp only [TT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
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
        Option.some.injEq, exists_eq_left', sr, equalExact_eq_decide]
      simp only [Del, tt]

/-- The static size check after the deleted element. -/
theorem size_check1 {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S)
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) ∧ (sz = Bool.true → ∀ w, TT t n S w → i < List.length w) := by
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
  simp only [filter_dyn, filter_tdyn, rkd, rto, rsz] at run
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    cases kd <;> cases sz <;> simp [boolAtom, Erlang.erlang.«/=/2»] at run <;>
      subst run <;> simp
  rw [bp_true.mpr to] at run
  cases kd
  · simp [boolAtom, Erlang.erlang.«/=/2»] at run; subst run; simp
  cases sz
  · simp [boolAtom, Erlang.erlang.«/=/2»] at run; subst run; simp
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
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, rR', Lynx.Except.ok_bind, equal_eq_decide] at run
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2] at run
    simp [Term.true] at run
    subst run; simp
  have eR : R' = r := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
    · exact absurd ⟨ec, es⟩ both
    all_goals
      first
      | rw [bp_true.mpr ec, bp_false.mpr es] at run
      | rw [bp_false.mpr ec, bp_true.mpr es] at run
      | rw [bp_false.mpr ec, bp_false.mpr es] at run
      simp [Term.true] at run
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
    TOnly t n X ∧ (∀ w, TT t n X w → i < List.length w) ∧ DE (level t n).E (.map R) ∧
      (∀ v : PN t n, denD (.map R) v → v.1.1 = "tuple") ∧ ∀ w, TT t n R w ↔ Del (TT t n X) i w := by
  obtain ⟨res, rres, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨only, short, r, rfl, tr, sr⟩⟩ := delete_cases hX i hm
  · rw [run] at rres; cases rres
  · rw [run] at rres; cases rres
  rw [run] at rres
  cases rres
  have long : ∀ w, TT t n X w → i < List.length w := fun w hw =>
    Classical.byContradiction fun h => short ⟨w, hw, by omega⟩
  refine ⟨only, long, Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩, fun v hv => ?_, fun w => ?_⟩
  · rw [denD_map] at hv
    by_cases h : v.1.1 = "tuple"
    · exact h
    · simp [mapLookup, h, dn_none] at hv
  · simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
      Option.some.injEq, exists_eq_left', sr, equalExact_eq_decide]
    simp only [Del, TT, mapLookup, equalExact_eq_decide]

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
        (tpt (t := t) (n := n) u) ∧ i < List.length u) ∨ TT t n (rmDyn X) u) i u := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX : DE (level t n).E (.map X) := GC.static gX hD
    obtain ⟨-, long, dR, oR, tR⟩ := del_static_pts dX i (by omega) run
    rw [rmDyn_static hD, upper_tc dX, upper_tc dR]
    have pq : ∀ u, TT t n X u ↔ (denD (.map X) (tpt (t := t) (n := n) u) ∧ i < List.length u) ∨ TT t n X u := fun u => by
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
    (∀ w, TT t n X w → i < List.length w) ∧ DE (level t n).E (.map Y) ∧ (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧
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
      simp [getMapKeys_single, Erlang.erlang.«==/2», sY, hA, ex, unfold_map, Erlang.maps.«put/3», alignT, cm]
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
    have get₂' : Elixir.Map.«get/3» (.map (List.filter (fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst)
        (.atom "dynamic") entry.fst = Ordering.eq)) X)) (.atom "tuple") (.atom "bdd_bot") = .ok b₂ := get₂
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

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_fetch_static/2` on a static type with a tuple field, empty or not. -/
theorem static_fetch_any (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_static/2» (D (n + 2)) (.map X) (.integer i) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, List.length v₁ = i → denTF E den b (v₁ ++ y :: v₂) = Bool.true → den e y) ∧
      (o = Bool.true ↔ ∃ v, denTF E den b v = Bool.true ∧ List.length v ≤ i) ∧
      (∀ y, den e y → ∃ v₁ v₂, List.length v₁ = i ∧ denTF E den b (v₁ ++ y :: v₂) = Bool.true) := by
  by_cases ne : ∃ v, denTF E den b v = Bool.true
  · exact static_fetch ef hn hb fb ne i
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, hl⟩ := tfield_three fb e₀
    have sem : ∀ v, denTF E den (.tuple #[.integer k, .atom tag, Term.list l]) v = Bool.true ↔
        InT den (tag == "closed") l v := fun v => by rw [denTF_leaf ef g hl, vT_lit ef g hl]
    -- The literal holds no tuples, so one of its elements is empty.
    obtain ⟨c, check, full, -⟩ := elements_exact ef.opsU ef.msemZ rfl l hl
    have c_true : c = Bool.true := by
      cases c
      · exfalso
        have each : ∀ e ∈ l, ∃ y, den e y := fun e me => full_witness ef.msemZ rfl (full rfl e me)
        rcases g with rfl | rfl
        · obtain ⟨w, hw, -⟩ := inT_witness_open (Classical.choice ef.inhabited) each 0
          exact ne ⟨w, (sem w).mpr (by simpa using hw)⟩
        · obtain ⟨w, hw⟩ := inT_exists_closed each
          exact ne ⟨w, (sem w).mpr (by simpa using hw)⟩
      · rfl
    subst c_true
    refine ⟨.map [], Bool.false, ?_, ef.none, fun v₁ y v₂ _ h => absurd ⟨_, h⟩ ne,
      ⟨fun h => (by cases h), fun ⟨v, hv, _⟩ => absurd ⟨v, hv⟩ ne⟩, fun y hy => absurd hy (ef.den_none y)⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
    simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«tuple_fetch_leaf/3», check (n + 2) (by omega), boolAtom]
  · have wb : Bdd (TLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := bdd_fetch (den := den) ef hn wb i
    refine ⟨e, o, ?_, he, s₁, s₂, s₃⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
    rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · simp [getMapKeys_single, hb, run]
    · simp [getMapKeys_single, hb, run]
    · exact absurd ⟨_, _, _, rfl⟩ three
    · simp [getMapKeys_single, hb, run]

end

section
variable {V : Type}

/-- `tuple_fetch_static/2` at an index of tuples `Q`: the values there, and whether some tuple is not longer. -/
def FetchSem (E : Term → Prop) (den : Term → V → Prop) (Q : List V → Prop) (i : Nat) (e : Term) (o : Bool) : Prop :=
  E e ∧ (∀ v₁ y v₂, List.length v₁ = i → Q (v₁ ++ y :: v₂) → den e y) ∧ (o = Bool.true ↔ ∃ v, Q v ∧ List.length v ≤ i) ∧
    (∀ y, den e y → ∃ v₁ v₂, List.length v₁ = i ∧ Q (v₁ ++ y :: v₂))

end

section
variable {t : Term} {n : Nat}

/-- `tuple_fetch_static/2` on a static type of the next level. -/
theorem fetch_static_sem {Y : Term} (hY : DE (level t n).E Y) (i : Nat) {m : Nat} (hm : (level t n).K + 3 ≤ m) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_static/2» (D m) Y (.integer i) = .ok (.tuple #[e, boolAtom o]) ∧
      FetchSem (level t n).E (level t n).den (fun v => denD Y (tpt (t := t) (n := n) v)) i e o := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have ef := (level t n).ef
  rcases hY with rfl | ⟨DX, rfl, sX⟩
  · refine ⟨.atom "term", Bool.true, ?_, ef.term, fun _ y _ _ _ => ef.den_term y,
      ⟨fun _ => ⟨[], denD_term _, by simp⟩, fun _ => rfl⟩, fun y _ => ⟨List.replicate i y, [], by simp, denD_term _⟩⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»; rfl
  cases hb : mapLookup DX (.atom "tuple") with
  | none =>
    have no : ∀ v, ¬denD (.map DX) (tpt (t := t) (n := n) v) := fun v h => by
      rw [denD_tpt] at h; obtain ⟨b, e, -⟩ := h; rw [hb] at e; cases e
    refine ⟨.map [], Bool.false, ?_, ef.none, fun v₁ y v₂ _ h => absurd h (no _),
      ⟨fun h => (by cases h), fun ⟨v, hv, _⟩ => absurd hv (no v)⟩, fun y hy => absurd hy (ef.den_none y)⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
    simp [getMapKeys_single, hb, boolAtom]
  | some b =>
    have tt : ∀ v, denD (.map DX) (tpt (t := t) (n := n) v) ↔
        denTF (level t n).E (level t n).den b v = Bool.true := fun v => by rw [denD_tpt]; simp [TT, hb]
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ :=
      static_fetch_any ef (n := k) (by omega) hb (fieldC_tuple (sX.fields "tuple" b hb)) i
    refine ⟨e, o, run, he, fun v₁ y v₂ len h => s₁ v₁ y v₂ len ((tt _).mp h), ?_, fun y hy => ?_⟩
    · rw [s₂]; simp only [tt]
    · obtain ⟨v₁, v₂, len, h⟩ := s₃ y hy
      exact ⟨v₁, v₂, len, (tt _).mpr h⟩

end

section
variable {t : Term} {d : Nat}

/-- `tuple_fetch/2` on a gradual type, when it gives a type: the fetch from the static part, with the fetch from the
dynamic part in its upper bound, optional when either is. -/
theorem fetch_grad {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) (i : Nat) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m)
    {fl ty : Term} (run : Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok (.tuple #[fl, ty])) :
    ∃ dt dO st sO, FetchSem (level t (d + 1)).E (level t (d + 1)).den (fun v => denD Dy (tpt (t := t) (n := d + 1) v)) i dt dO ∧
      FetchSem (level t (d + 1)).E (level t (d + 1)).den (TT t (d + 1) (rmDyn X)) i st sO ∧
      (∃ y, (level t (d + 1)).den dt y) ∧ fl = boolAtom (sO || dO) ∧ GC (level t d) ty ∧
      (∀ y : PN t d, denD ty y ↔ (level t (d + 1)).den st y) ∧
      (∀ y : PN t d, denD (upper ty) y ↔ (level t (d + 1)).den dt y ∨ (level t (d + 1)).den st y) ∧
      ∀ v : PN t (d + 1), denD (.map (rmDyn X)) v → v.1.1 = "tuple" := by
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
  -- The fetches from both parts.
  obtain ⟨dt, dO, rdt, sdt⟩ := fetch_static_sem dDy i (m := k + 3) (by omega)
  obtain ⟨st, sO, rst, sst⟩ := fetch_static_sem dS i (m := k + 3) (by omega)
  have sst' : FetchSem (level t (d + 1)).E (level t (d + 1)).den (TT t (d + 1) (rmDyn X)) i st sO := by
    have e : (fun v => denD (.map (rmDyn X)) (tpt (t := t) (n := d + 1) v)) = TT t (d + 1) (rmDyn X) :=
      funext fun v => propext (denD_tpt v)
    rw [e] at sst; exact sst
  obtain ⟨eb, reb, seb⟩ := ef.empty_pub sdt.1
  obtain ⟨c₁, hc₁, sc₁, cases₁⟩ := el_canon sdt.1
  obtain ⟨R, rR, gR, s₁, s₂⟩ := dyn_el_union hc₁ sst.1 (m := k + 3) (by omega)
  have kd : ∃ kd : Bool, Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom kd) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · exact ⟨Bool.true, rfl⟩
    · refine ⟨(mapLookup DX (.atom "tuple")).isSome, ?_⟩
      cases h : (mapLookup DX (.atom "tuple")).isSome <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, h]
  obtain ⟨kd, rkd⟩ := kd
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def] at run
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1»,
    Erlang.maps.«remove/2»] at run
  simp only [filter_tdyn, filter_dyn, rto, rkd, rdt, rst] at run
  refine ⟨dt, dO, st, sO, sdt, sst', ?_⟩
  by_cases to : ∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    cases kd <;> simp [boolAtom, Lynx.Except.andAlso] at run
  rw [bp_true.mpr to] at run
  cases kd
  · simp [boolAtom, Lynx.Except.andAlso] at run
  have reb' := reb (k + 3) (by omega)
  simp only [boolAtom, Lynx.Except.andAlso] at run
  simp only [reb', Lynx.Except.ok_bind] at run
  cases eb
  rotate_left
  · simp [boolAtom] at run
  have ne : ∃ y, (level t (d + 1)).den dt y :=
    Classical.byContradiction fun h => absurd (seb.mpr fun y hy => h ⟨y, hy⟩) (by simp)
  refine ⟨ne, ?_⟩
  have ok : boolAtom (sO || dO) = fl ∧ R = ty := by
    rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
    · rcases de with rfl | ⟨Z, rfl, sZ⟩
      · cases sO <;> cases dO <;> simpa [boolAtom, Lynx.Term.isMember, Lynx.Except.orElse, getMapKeys, rR] using run
      · cases sO <;> cases dO <;>
          simpa [boolAtom, Lynx.Term.isMember, Lynx.Except.orElse, getMapKeys_single, sZ.static, rR] using run
    · obtain ⟨q, SS, rfl⟩ := node_tuple hn
      have ex := expand_isT hn (k + 2)
      obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
      rw [eY] at ex rR
      have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 3)) (.map Y) =
          .ok (.map [(.atom "dynamic", .map Y)]) := by
        unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
      have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
      cases sO <;> cases dO <;>
        simpa [boolAtom, Lynx.Term.isMember, Lynx.Except.orElse, gt, ex, unfold_map, dY, rR] using run
  obtain ⟨rfl, rfl⟩ := ok
  exact ⟨rfl, gR, s₁, fun y => (s₂ y).trans (or_congr_left (sc₁ y).symm),
    fun v hv => Classical.byContradiction fun ne => to v ((rt v).mpr ⟨hv, ne⟩)⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Updates of gradual types: the dynamic part is updated with errors computed as for gradual types, which change
neither the values nor the maps of the update. -/

/-- Accumulators of updates that agree on their value and maps. -/
def Rel4 (a b : Term) : Prop := ∃ v bd e₁ f₁ e₂ f₂, a = .tuple #[v, bd, e₁, f₁] ∧ b = .tuple #[v, bd, e₂, f₂]

/-- One step of `map_update_named_keys/8` gives the same value and maps whether the type is static or not. -/
theorem named_step_rel (d : Dispatcher) (dnf op req bld ov fo key : Term) (s₁ s₂ : Term)
    {v bd e₁ f₁ e₂ f₂ r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₁ bld ov fo key
      (.tuple #[v, bd, e₁, f₁]) = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₂ bld ov fo key
      (.tuple #[v, bd, e₂, f₂]) = .ok r₂) : Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at h₁ h₂
  cases hk : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov with
  | error e => simp [hk] at h₁
  | ok t =>
    simp only [hk, Lynx.Except.ok_bind] at h₁ h₂
    split at h₁
    case h_2 => simp at h₁
    rename_i bds old
    simp only at h₂
    cases hb : Erlang.erlang.«++/2» bds bd with
    | error e => simp [hb] at h₁
    | ok B =>
      simp only [hb, Lynx.Except.ok_bind] at h₁ h₂
      by_cases hn : old = .atom "nil"
      · subst hn
        simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
        subst h₁ h₂
        exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      by_cases ht : ∃ value opt, old = .tuple #[value, opt]
      · obtain ⟨value, opt, rfl⟩ := ht
        simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure] at h₁ h₂
        split at h₁
        · simp at h₁
        rename_i b16 h16
        simp only [h16] at h₂
        simp only [Lynx.Except.tryWith] at h₁ h₂
        split at h₁
        · -- The old value has values: the value is updated.
          rename_i hm
          simp only [hm] at h₂
          cases hu : Elixir.Module.Types.Descr.«opt_union/2» d value v with
          | error e => simp [hu] at h₁
          | ok U =>
            simp only [hu] at h₁ h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[U, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[U, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
        · rename_i hx
          cases hm : b16.isMember [Term.atom "false", Term.atom "nil"] with
          | atom a =>
            by_cases ha : a = "true"
            · subst ha; exact (hx hm).elim
            · simp only [hm] at h₂
              obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
                clear h₂
                repeat' split at h₁
                all_goals first
                  | (simp at h₁; done)
                  | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
              obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
                clear h₁
                split at h₂
                · simp_all
                repeat' split at h₂
                all_goals first
                  | (simp at h₂; done)
                  | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
              exact ⟨_, _, _, _, _, _, rfl, rfl⟩
          | _ =>
            simp only [hm] at h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      · split at h₁
        · exact absurd rfl hn
        · exact absurd ⟨_, _, rfl⟩ ht
        · simp at h₁

theorem foldl1_rel4 (d : Dispatcher) (f₁ f₂ : Term)
    (hs : ∀ x a b a' b', Rel4 a b → d.pure f₁ #[x, a] = .ok a' → d.pure f₂ #[x, b] = .ok b' → Rel4 a' b') :
    ∀ (l a b : Term) {r₁ r₂ : Term}, Rel4 a b → Erlang.lists.«foldl_1/3» d f₁ a l = .ok r₁ →
      Erlang.lists.«foldl_1/3» d f₂ b l = .ok r₂ → Rel4 r₁ r₂
  | .cons x l, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only at h₁ h₂
    cases e₁ : d.pure f₁ #[x, a] with
    | error e => rw [e₁] at h₁; cases h₁
    | ok a' =>
      cases e₂ : d.pure f₂ #[x, b] with
      | error e => rw [e₂] at h₂; cases h₂
      | ok b' =>
        rw [e₁] at h₁; rw [e₂] at h₂
        exact foldl1_rel4 d f₁ f₂ hs l a' b' (hs x a b a' b' hab e₁ e₂) (by simpa using h₁) (by simpa using h₂)
  | .nil, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
    subst h₁ h₂; exact hab
  | .atom _, _, _, _, _, _, h₁, _ | .integer _, _, _, _, _, _, h₁, _ | .float _, _, _, _, _, _, h₁, _
  | .tuple _, _, _, _, _, _, h₁, _ | .map _, _, _, _, _, _, h₁, _ | .bitstring _ _ _, _, _, _, _, _, h₁, _
  | .function _ _ _ _ _, _, _, _, _, _, h₁, _ | .pid _, _, _, _, _, _, h₁, _ | .reference _, _, _, _, _, _, h₁, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁; simp at h₁

theorem foldl_rel4 (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (hs : ∀ x a b a' b', Rel4 a b → d.pure (.function false mo nm 2 c₁) #[x, a] = .ok a' →
      d.pure (.function false mo nm 2 c₂) #[x, b] = .ok b' → Rel4 a' b')
    (l a b : Term) {r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₁) a l = .ok r₁)
    (h₂ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₂) b l = .ok r₂) : Rel4 r₁ r₂ := by
  have conv : ∀ c acc r, Erlang.lists.«foldl/3» d (.function false mo nm 2 c) acc l = .ok r →
      Erlang.lists.«foldl_1/3» d (.function false mo nm 2 c) acc l = .ok r := by
    intro c acc r h
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»] at h
    rw [Erlang.lists.«foldl_1/3».eq_def]
    cases l <;> simp_all
  replace h₁ := conv _ _ _ h₁
  replace h₂ := conv _ _ _ h₂
  exact foldl1_rel4 d _ _ hs l a b hab h₁ h₂

theorem named_keys_rel (m : Nat) (dnf keys op req rt bo s₁ s₂ : Term) {a b r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req s₁ rt bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req s₂ rt bo = .ok r₂) :
    Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    refine foldl_rel4 _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    obtain ⟨v, bd, e₁', f₁', e₂', f₂', rfl, rfl⟩ := hab
    exact named_step_rel _ _ _ _ _ _ _ _ _ _ e₁ e₂

/-- `map_update_static_dnf/6` gives the same value and maps whether the type is static or not. -/
theorem dnf_rel (m : Nat) (bdd dnf split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₂ = .ok r₂) :
    Rel4 r₁ r₂ := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁
    · simp at h₁
    rename_i v₁ n₁
    split at h₂
    · simp at h₂
    rename_i v₂ n₂
    have r₀ := named_keys_rel _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, _, rfl, rfl⟩ n₁ n₂
    split at h₁
    · simp at h₁
    rename_i w₁ n₁'
    split at h₂
    · simp at h₂
    rename_i w₂ n₂'
    obtain ⟨V, BD, e₁, f₁, e₂, f₂, rfl, rfl⟩ := named_keys_rel _ _ _ _ _ _ _ _ _ r₀ n₁' n₂'
    simp only at h₁ h₂
    split at h₁
    · simp at h₁
    rename_i u hu
    simp only [hu] at h₂
    by_cases hbot : u = .atom "bdd_bot"
    · subst hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩
    · split at h₁
      · exact absurd rfl hbot
      split at h₂
      · exact absurd rfl hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem static_rel_ne (m : Nat) (descr split op rt s₁ s₂ : Term) (hd : descr ≠ .atom "term") {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (dnf_rel _ _ _ _ _ _ _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)

/-- `map_update_static/5` gives the same value and maps whether the type is static or not. -/
theorem static_rel (m : Nat) (descr split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_rel_ne m _ split op rt s₁ s₂ (by simp) h₁ h₂
  · exact static_rel_ne m descr split op rt s₁ s₂ h h₁ h₂

/-- The gradual branch of `map_update_unchecked/4`: the update of the static part united with the dynamic update of the
dynamic part. -/
theorem grad_upd_inv {X : List (Term × Term)} {Dy : Term} (hD : mapLookup X (.atom "dynamic") = some Dy)
    {split op rt : Term} {m : Nat} {T R er : Term}
    (hdyn : ∀ Td Yd ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") =
      .ok (.tuple #[Td, Yd, ed, fd]) → ∃ Y', Yd = .map Y' ∧ mapLookup Y' (.atom "dynamic") = none)
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map X) split op rt =
      .ok (.tuple #[T, R, er])) :
    ∃ Yd res sd, (∃ Td ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") =
        .ok (.tuple #[Td, .map Yd, ed, fd])) ∧ mapLookup Yd (.atom "dynamic") = none ∧
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f]) ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) = .ok R := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hD, equalExact_eq_decide] at run
  simp only [filter_dyn, bind, Except.bind, pure, Except.pure] at run
  have fun1 : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, R, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun1 _)
  cases hd₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") with
  | error e => rw [hd₀] at run; simp at run
  | ok r =>
    rw [hd₀] at run
    obtain ⟨Td, Yd₀, ed, fd, rfl⟩ : ∃ Td Yd ed fd, r = .tuple #[Td, Yd, ed, fd] := by
      by_cases h4 : ∃ Td Yd ed fd, r = .tuple #[Td, Yd, ed, fd]
      · exact h4
      · exfalso
        simp only at run
        split at run
        · exact h4 ⟨_, _, _, _, rfl⟩
        · exact fun1 _ run
    obtain ⟨Yd, rfl, sYd⟩ := hdyn Td Yd₀ ed fd hd₀
    generalize fd.isMember [Term.atom "false", Term.atom "nil"] = fm at run
    simp only at run
    cases hs₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") with
    | error e => rw [hs₀] at run; simp at run
    | ok res =>
      rw [hs₀] at run
      have gk : getMapKeys [Term.atom "dynamic"] (.map Yd) = [] := by simp [getMapKeys_single, sYd]
      obtain ⟨sd, hsd⟩ : ∃ sd, (res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f] := by
        by_cases hb : res = .atom "badmap"
        · exact ⟨_, Or.inl ⟨hb, rfl⟩⟩
        · by_cases h4 : ∃ a sd e f, res = .tuple #[a, sd, e, f]
          · obtain ⟨a, sd, e, f, rfl⟩ := h4
            exact ⟨sd, Or.inr ⟨a, e, f, rfl⟩⟩
          · exfalso
            simp only at run
            repeat' split at run
            all_goals simp_all
      refine ⟨Yd, res, sd, ⟨Td, ed, fd, rfl⟩, sYd, rfl, hsd, ?_⟩
      cases hR : Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) with
      | error err =>
        exfalso
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp at run; done)
          | (simp_all; done)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> first | (cases run; done) | simp_all)
      | ok R' =>
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp only at run
             exact congrArg Except.ok run.2.1.symm)
          | (simp at run; done)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> first | (cases run; done) | simp_all)

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The operations of `map_update/5` with a static value, or deleting. -/
def OpK (E : Term → Prop) (den : Term → V → Prop) (op : Term) : Prop :=
  (∃ v, E v ∧ (v = .atom "term" ∨ ∃ Z, v = .map Z) ∧
    (op = forceOp v ∨ ((∃ x, den v x) ∧ ∃ keep, op = keepOp v keep))) ∨
  ∃ md, Mode md ∧ op = cOp (.map []) Bool.true md

/-- Results of `map_update_static/5` with maps of a single field. -/
def UpdRes (E : Term → Prop) (r : Term) : Prop :=
  r = .atom "badmap" ∨ ∃ T Y e f, r = .tuple #[T, Y, e, f] ∧ (Y = .map [] ∨ ∃ r', Y = .map [(.atom "map", r')] ∧ MField E r')

/-- `map_update_static/5` on a map field, for either flag, gives no map or maps of one field. -/
theorem field_wf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b)
    {op : Term} (hop : OpK E den op) (st : Term) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) : UpdRes E r := by
  -- The update as a static type.
  obtain ⟨r', h', s'⟩ : ∃ r', Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "true") = .ok r' ∧ UpdRes E r' := by
    rcases hop with ⟨v, hv, sv, rfl | ⟨vne, keep, rfl⟩⟩ | ⟨md, hmd, rfl⟩
    · obtain ⟨res, run, hres⟩ := dput_update_static ef hn hv sv ok (fun N e => by rw [nr N e]; rfl) hNa hb fb
      obtain ⟨res', run', ⟨rfl, bad⟩ | ⟨Y, f, rfl, T, er, run₂, -⟩⟩ := upd_old_static ef hn hv sv ok nr hNa hb fb
      · exact ⟨_, bad, Or.inl rfl⟩
      · rw [run] at run'; cases run'
        refine ⟨_, run₂, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hres with ⟨e, -⟩ | ⟨Y', f', e, -, -, hY⟩
        · cases e
        · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
          obtain ⟨-, rfl, -, rfl, -⟩ := e
          rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ :=
        kr_update_static ef hn hv sv vne keep ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ := del_update_static (st := Bool.true) ef hn hmd ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
  rcases static_rel (n + 5) _ _ _ _ _ _ h h' with rfl | ⟨v, bd, e₁, f₁, e₂, f₂, rfl, rfl⟩
  · exact s'
  · rcases s' with e | ⟨T, Y, e, f, e', hY⟩
    · cases e
    · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact Or.inr ⟨_, _, _, _, rfl, hY⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_update_static/5` on a static type of the next level, for either flag, gives no map or maps of one field. -/
theorem type_wf {Dy : Term} (hDy : DE (level t n).E Dy) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 10 ≤ m) (st : Term)
    {r : Term} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D m) Dy
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) :
    UpdRes (level t n).E r := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have ef := (level t n).ef
  rcases hDy with rfl | ⟨DX, rfl, sX⟩
  · rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
    have gk : getMapKeys [Term.atom "map"] (.atom "term") = [] := by simp [getMapKeys]
    simp only [gk] at h
    exact field_wf ef (n := k) (by omega) ok nr hNa (X := [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
      (by simp [mapLookup]) (Or.inl ⟨61102469, rfl⟩) hop st h
  · cases hb : mapLookup DX (.atom "map") with
    | some b => exact field_wf ef (n := k) (by omega) ok nr hNa hb (fieldC_map (sX.fields "map" b hb)) hop st h
    | none =>
      rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
      simp [getMapKeys_single, hb] at h
      subst h
      exact Or.inr ⟨_, _, _, _, rfl, Or.inl rfl⟩

end

/-- The static branch of `map_update_unchecked/4`. -/
theorem static_upd_inv {S : List (Term × Term)} (hS : mapLookup S (.atom "dynamic") = none)
    {split op rt : Term} {m : Nat} {T Y er : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map S) split op rt =
      .ok (.tuple #[T, Y, er])) :
    ∃ f, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") =
      .ok (.tuple #[T, Y, er, f]) := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hS] at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  have fun0 : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, Y, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun0 _)
  cases hs : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") with
  | error e => rw [hs] at run; simp at run
  | ok r =>
    rw [hs] at run
    simp only at run
    split at run
    · rename_i T' Y' er' f'
      simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run
      split at run
      · simp at run
      · simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
        obtain ⟨rfl, rfl, rfl, -⟩ := run
        exact ⟨f', rfl⟩
    · exact absurd run (fun0 _)

section
variable {t : Term} {n : Nat}

theorem updRes_de {r : Term} (h : UpdRes (level t n).E r) (nb : r ≠ .atom "badmap") :
    ∃ T Y e f, r = .tuple #[T, .map Y, e, f] ∧ DE (level t n).E (.map Y) ∧ mapLookup Y (.atom "dynamic") = none := by
  rcases h with rfl | ⟨T, Y, e, f, rfl, rfl | ⟨r', rfl, fr⟩⟩
  · exact absurd rfl nb
  · exact ⟨T, [], e, f, rfl, Or.inr ⟨_, rfl, descrC_nil⟩, by simp [mapLookup]⟩
  · exact ⟨T, _, e, f, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, by simp [mapLookup]⟩

/-- Updating a gradual type with a static value at static keys gives, as lower bound, the update of its lower bound. -/
theorem lower_core {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T R er T' Y er' : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T, R, er]))
    (runL : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (rmDyn X))
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T', Y, er'])) :
    ∃ R₀, Elixir.Module.Types.Descr.«lower_bound/1» (D m) R = .ok R₀ ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) R₀ Y = .ok (.atom "true") := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have sS : mapLookup (rmDyn X) (.atom "dynamic") = none := by simp [lookup_rmDyn]
  have dS : DE (level t n).E (.map (rmDyn X)) := gX.low_tc
  -- The update of the lower bound.
  obtain ⟨fL, hL⟩ := static_upd_inv sS runL
  obtain ⟨T₀, YY, e₀, f₀, eL, dY, -⟩ := updRes_de (type_wf dS ok nr hNa hop (by omega) _ hL) (by simp)
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eL
  obtain ⟨-, rfl, -⟩ := eL
  have ef := ef_next t n
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    rw [rmDyn_static hD] at runL
    rw [runL] at run
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
    obtain ⟨-, rfl, -⟩ := run
    refine ⟨.map (rmDyn YY), lower_bound_run (Or.inr ⟨_, rfl⟩), ?_⟩
    have dY' : DE (level t n).E (.map (rmDyn YY)) := (GC.tc dY).low_tc
    exact elem_equal ef dY' dY (fun q => denD_rmDyn YY q) (by omega)
  | some Dy =>
    obtain ⟨dDy, -⟩ : DE (level t n).E Dy ∧ True := by
      rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, -, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, trivial⟩
    have hdyn : ∀ Td Yd ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 1)) Dy
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "false") =
          .ok (.tuple #[Td, Yd, ed, fd]) → ∃ Y', Yd = .map Y' ∧ mapLookup Y' (.atom "dynamic") = none := by
      intro Td Yd ed fd h
      obtain ⟨_, Y', _, _, e, -, sYd⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ h) (by simp)
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
      exact ⟨Y', e.2.1, sYd⟩
    obtain ⟨Yd, res, sd, ⟨Td, ed, fd, hdy⟩, -, hres, hsd, hR⟩ := grad_upd_inv hD hdyn run
    rw [hL] at hres
    cases hres
    rcases hsd with ⟨e, -⟩ | ⟨a, e, f, e'⟩
    · cases e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
    obtain ⟨-, rfl, -⟩ := e'
    obtain ⟨T₁, Yd', e₁, f₁, eD, dYd, -⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ hdy) (by simp)
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eD
    obtain ⟨-, eYd, -⟩ := eD
    cases eYd
    -- The union of the static update and the dynamic one.
    have gA : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) := by
      refine Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, ?_, fun v hv => ?_⟩
      · rw [show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]]; exact descrC_nil
      · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
        simp [denD_map, mapLookup, dn_none] at hv
    have noA : ∀ v : PN t n, ¬denD (.map [(.atom "dynamic", .map Yd)]) v := fun v hv => by
      rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
      simp [denD_map, mapLookup, dn_none] at hv
    obtain ⟨c, gc, rc, sc, -⟩ := gc_opt_union (GC.tc dY) gA [] (m := k + 1) (by omega)
    rw [show Elixir.Module.Types.Descr.«opt_union/2» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) =
      Elixir.Module.Types.Descr.«opt_union/3» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) (.map []) from rfl,
      rc] at hR
    cases hR
    refine ⟨lower R, lower_bound_run gc.shape, ?_⟩
    exact elem_equal ef gc.low_tc dY (fun q => (denD_lower R q).trans ((sc q).trans (or_iff_left (noA q)))) (by omega)

end


/-- `map_update/5` with a static value updates with the value at the split of the keys. -/
theorem upd5_val {m : Nat} (X : Term) {key v mode s : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key v mode (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], mode]) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, Lynx.Term.getMapKeys]
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, getMapKeys_single, sZ]

/-- `map_update/5` deleting updates with no value at the split of the keys. -/
theorem upd5_del {m : Nat} (X : Term) {key s : Term} {md : String}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key (.atom "delete") (.atom md) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s (cOp (.map []) Bool.true md) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk] <;> rfl


/-! Splits of gradual keys: required and optional keys and domains update with the same maps as when all are
required, in the order `map_update_static_dnf/6` reads them. -/

/-- Accumulators of updates that agree on their maps. -/
def RelB (a b : Term) : Prop := ∃ v₁ bd e₁ f₁ v₂ e₂ f₂, a = .tuple #[v₁, bd, e₁, f₁] ∧ b = .tuple #[v₂, bd, e₂, f₂]

theorem relB_mk (v₁ bd e₁ f₁ v₂ e₂ f₂ : Term) : RelB (.tuple #[v₁, bd, e₁, f₁]) (.tuple #[v₂, bd, e₂, f₂]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl⟩

/-- A step of `map_update_named_keys/8` gives the maps of the key prepended to the accumulated ones. -/
theorem named_step_maps (d : Dispatcher) (dnf op req st bld ov fo key : Term) {v bd e f r : Term}
    (h : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req st bld ov fo key
      (.tuple #[v, bd, e, f]) = .ok r) :
    ∃ bds old B, Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov = .ok (.tuple #[bds, old]) ∧
      Erlang.erlang.«++/2» bds bd = .ok B ∧ ∃ a e' f', r = .tuple #[a, B, e', f'] := by
  simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at h
  cases hk : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov with
  | error e => simp [hk] at h
  | ok t =>
    simp only [hk, Lynx.Except.ok_bind] at h
    split at h
    · rename_i bds old
      cases hb : Erlang.erlang.«++/2» bds bd with
      | error e => simp [hb] at h
      | ok B =>
        refine ⟨bds, old, B, rfl, hb, ?_⟩
        simp only [hb, Lynx.Except.ok_bind] at h
        simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
          Lynx.Except.tryWith] at h
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [Except.ok.injEq] at h; subst h; exact ⟨_, _, _, rfl⟩)
    · simp at h

theorem named_step_relB (d : Dispatcher) (dnf op req₁ req₂ s₁ s₂ bld ov fo key : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₁ s₁ bld ov fo key a = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₂ s₂ bld ov fo key b = .ok r₂) :
    RelB r₁ r₂ := by
  obtain ⟨v₁, bd, e₁, f₁, v₂, e₂, f₂, rfl, rfl⟩ := hab
  obtain ⟨bds, old, B, k₁, b₁, a, e, f, rfl⟩ := named_step_maps d dnf op req₁ s₁ bld ov fo key h₁
  obtain ⟨bds', old', B', k₂, b₂, a', e', f', rfl⟩ := named_step_maps d dnf op req₂ s₂ bld ov fo key h₂
  rw [k₁] at k₂
  simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at k₂
  obtain ⟨rfl, rfl⟩ := k₂
  rw [b₁] at b₂; cases b₂
  exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩

theorem foldl1_relP (P : Term → Term → Prop) (d : Dispatcher) (f₁ f₂ : Term)
    (hs : ∀ x a b a' b', P a b → d.pure f₁ #[x, a] = .ok a' → d.pure f₂ #[x, b] = .ok b' → P a' b') :
    ∀ (l a b : Term) {r₁ r₂ : Term}, P a b → Erlang.lists.«foldl_1/3» d f₁ a l = .ok r₁ →
      Erlang.lists.«foldl_1/3» d f₂ b l = .ok r₂ → P r₁ r₂
  | .cons x l, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only at h₁ h₂
    cases e₁ : d.pure f₁ #[x, a] with
    | error e => rw [e₁] at h₁; cases h₁
    | ok a' =>
      cases e₂ : d.pure f₂ #[x, b] with
      | error e => rw [e₂] at h₂; cases h₂
      | ok b' =>
        rw [e₁] at h₁; rw [e₂] at h₂
        exact foldl1_relP P d f₁ f₂ hs l a' b' (hs x a b a' b' hab e₁ e₂) (by simpa using h₁) (by simpa using h₂)
  | .nil, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
    subst h₁ h₂; exact hab
  | .atom _, _, _, _, _, _, h₁, _ | .integer _, _, _, _, _, _, h₁, _ | .float _, _, _, _, _, _, h₁, _
  | .tuple _, _, _, _, _, _, h₁, _ | .map _, _, _, _, _, _, h₁, _ | .bitstring _ _ _, _, _, _, _, _, h₁, _
  | .function _ _ _ _ _, _, _, _, _, _, h₁, _ | .pid _, _, _, _, _, _, h₁, _ | .reference _, _, _, _, _, _, h₁, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁; simp at h₁

theorem foldl_relP (P : Term → Term → Prop) (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (hs : ∀ x a b a' b', P a b → d.pure (.function false mo nm 2 c₁) #[x, a] = .ok a' →
      d.pure (.function false mo nm 2 c₂) #[x, b] = .ok b' → P a' b')
    (l a b : Term) {r₁ r₂ : Term} (hab : P a b)
    (h₁ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₁) a l = .ok r₁)
    (h₂ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₂) b l = .ok r₂) : P r₁ r₂ := by
  have conv : ∀ c acc r, Erlang.lists.«foldl/3» d (.function false mo nm 2 c) acc l = .ok r →
      Erlang.lists.«foldl_1/3» d (.function false mo nm 2 c) acc l = .ok r := by
    intro c acc r h
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»] at h
    rw [Erlang.lists.«foldl_1/3».eq_def]
    cases l <;> simp_all
  exact foldl1_relP P d _ _ hs l a b hab (conv _ _ _ h₁) (conv _ _ _ h₂)

/-- `map_update_named_keys/8` gives the same maps whatever the keys' requirement and the static flag. -/
theorem named_keys_relB (m : Nat) (dnf keys op rt bo req₁ req₂ s₁ s₂ : Term) {a b r₁ r₂ : Term} (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req₁ s₁ rt bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req₂ s₂ rt bo = .ok r₂) :
    RelB r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    refine foldl_relP RelB _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    exact named_step_relB _ _ _ _ _ _ _ _ _ _ _ hab e₁ e₂

/-- `map_update_named_keys/8` over appended keys updates the first keys and then the others. -/
theorem named_keys_append (m : Nat) (acc dnf op req st rt bo : Term) (A B : List Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list (A ++ B)) op req st rt bo =
      (Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list A) op req st rt bo >>=
        fun r => Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) r dnf (Term.list B) op req st rt bo) := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8»]
  cases h₁ : Erlang.erlang.«element/2» (.integer 2) op with
  | error e => simp
  | ok o =>
    cases h₂ : Erlang.erlang.«==/2» o (.atom "force") with
    | error e => simp [h₂]
    | ok fo =>
      cases h₃ : Lynx.Except.orElse (Except.ok rt) (Erlang.erlang.«not/1» fo) true with
      | error e => simp [h₂, h₃]
      | ok ov =>
        simp only [h₂, h₃, Lynx.Except.ok_bind, pure, Except.pure, foldl_fun]
        rw [foldl1_list_append]

/-- Accumulators of `map_update_get_domains/5`: the fold from a fresh accumulator, and from one with flags and lists,
over the same keys; their accumulated values may differ. -/
def GShift (f : Term) (v mi : List Term) (x y : Term) : Prop :=
  ∃ g V Mi a b, y = .tuple #[g, Term.list V, Term.list Mi, b] ∧
    ((g = .atom "true" ∧ x = .tuple #[.atom "true", Term.list (V ++ v), Term.list (Mi ++ mi), a]) ∨
     (g = .atom "false" ∧ x = .tuple #[f, Term.list (V ++ v), Term.list (Mi ++ mi), a])) ∧ (V ≠ [] → g = .atom "true")

theorem gd_step_shift (d : Dispatcher) (dnf rt cb₁ cb₂ key : Term) (hcb : d.pure cb₁ #[] = d.pure cb₂ #[])
    {f : Term} {v mi : List Term} {x y x' y' : Term} (hxy : GShift f v mi x y)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₁ key x = .ok x')
    (h₂ : Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₂ key y = .ok y') :
    GShift f v mi x' y' := by
  obtain ⟨g, V, Mi, a, b, rfl, hx, hV⟩ := hxy
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5»] at h₁ h₂
    simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    generalize hc₁ : d.pure cb₁ #[] = c at h₁
    generalize hc₂ : d.pure cb₂ #[] = c₂ at h₂
    obtain rfl : c = c₂ := hc₁ ▸ hc₂ ▸ hcb
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
    all_goals (repeat' split at h₁) <;> (try (cases h₁; done))
    all_goals (repeat' split at h₂) <;> (try (simp at h₂; done))
    all_goals (try (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂))
  all_goals first
    | exact ⟨.atom "true", .atom "atom" :: V, Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl⟩
    | exact ⟨.atom "true", key :: V, Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩
    | exact ⟨.atom "true", V, .atom "atom" :: Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl⟩
    | exact ⟨.atom "false", V, .atom "atom" :: Mi, _, _, rfl, Or.inr ⟨rfl, rfl⟩, hV⟩
    | exact ⟨.atom "true", V, key :: Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩, hV⟩
    | exact ⟨.atom "false", V, key :: Mi, _, _, rfl, Or.inr ⟨rfl, rfl⟩, hV⟩
    | trace_state

theorem gd_fold_shift (m : Nat) (dnf rt cb₁ cb₂ : Term) (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[])
    {f : Term} {v mi : List Term} (l : Term) {x y x' y' : Term} (hxy : GShift f v mi x y)
    (h₁ : Erlang.lists.«foldl/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₁]) x l = .ok x')
    (h₂ : Erlang.lists.«foldl/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₂]) y l = .ok y') :
    GShift f v mi x' y' := by
  refine foldl_relP (GShift f v mi) _ (fun k a b a' b' hab e₁ e₂ => ?_) l x y hxy h₁ h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure] at e₁ e₂
  exact gd_step_shift _ _ _ _ _ _ hcb hab e₁ e₂

/-- Fresh accumulators of `map_update_get_domains/5`, related to themselves. -/
theorem gshift_fresh (a b : Term) :
    GShift (.atom "false") [] [] (.tuple #[.atom "false", .nil, .nil, a]) (.tuple #[.atom "false", .nil, .nil, b]) :=
  ⟨_, [], [], a, b, rfl, Or.inr ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

/-- A fold from a fresh accumulator and one from flags and lists. -/
theorem gshift_start (f : Term) (v mi : List Term) (a b : Term) :
    GShift f v mi (.tuple #[f, Term.list v, Term.list mi, a]) (.tuple #[.atom "false", .nil, .nil, b]) :=
  ⟨_, [], [], a, b, rfl, Or.inr ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

/-- `map_update_get_domains/5` gives a boolean flag, set when some domain is valid, and lists of domains. -/
theorem gd_bool (m : Nat) (dnf ks acc rt cb : Term) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks acc rt cb = .ok r) :
    ∃ g V Mi a, r = .tuple #[g, Term.list V, Term.list Mi, a] ∧ (g = .atom "true" ∨ g = .atom "false") ∧
      (V ≠ [] → g = .atom "true") := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at h
  obtain ⟨g, V, Mi, a, b, rfl, hx, hV⟩ := gd_fold_shift m dnf rt cb cb rfl ks (gshift_fresh acc acc) h h
  refine ⟨g, V, Mi, b, rfl, ?_, hV⟩
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gd_step_congr (d : Dispatcher) (dnf rt cb₁ cb₂ key x : Term) (hcb : d.pure cb₁ #[] = d.pure cb₂ #[]) :
    Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₁ key x =
      Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₂ key x := by
  simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5»]
  generalize hc₁ : d.pure cb₁ #[] = c₁
  generalize hc₂ : d.pure cb₂ #[] = c₂
  rw [hc₁, hc₂] at hcb
  subst hcb
  rfl

/-- `map_update_get_domains/5` over appended domains: the second domains fold on from the first. -/
theorem gd_append_rel (m : Nat) (dnf acc rt cb₁ cb₂ : Term) (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[])
    (A B : List Term) {g a R Y : Term} {V Mi : List Term}
    (hR : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list (A ++ B)) acc rt cb₂ = .ok R)
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list A) acc rt cb₁ =
      .ok (.tuple #[g, Term.list V, Term.list Mi, a]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list B) a rt cb₁ = .ok Y) :
    GShift g V Mi R Y := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind,
    foldl_fun] at hR hA hB
  rw [foldl1_list_append] at hR
  have congr : ∀ (l : Term) (x : Term), Erlang.lists.«foldl_1/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₂]) x l =
      Erlang.lists.«foldl_1/3» (D (m + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₁]) x l :=
    foldl1_congr _ _ _ fun k x => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      exact (gd_step_congr _ _ _ _ _ _ _ hcb).symm
  rw [congr, hA, Lynx.Except.ok_bind] at hR
  rw [← foldl_fun] at hR hB
  exact gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm (Term.list B) (gshift_start g V Mi a a) hR hB

/-- `map_update_get_domains/5` finds the same domains whatever value it starts from. -/
theorem gd_acc (m : Nat) (dnf ks rt cb a b : Term) {g x Y : Term} {V Mi : List Term}
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks a rt cb =
      .ok (.tuple #[g, Term.list V, Term.list Mi, x]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks b rt cb = .ok Y) :
    ∃ y, Y = .tuple #[g, Term.list V, Term.list Mi, y] := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at hA hB
  obtain ⟨g', V', Mi', a', b', rfl, hx, -⟩ := gd_fold_shift m dnf rt cb cb rfl ks (gshift_fresh a b) hA hB
  rcases hx with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, List.append_nil, and_true] at e <;>
    obtain ⟨rfl, e₁, e₂, rfl⟩ := e <;> exact ⟨b', by rw [list_inj e₁, list_inj e₂]⟩

/-- `map_update_get_domains/5` over appended domains, against lookups of each part from any values. -/
theorem gd_append_rel2 (m : Nat) (dnf acc accA accB rt cb₁ cb₂ : Term)
    (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[]) (A B : List Term) {g a R Y : Term} {V Mi : List Term}
    (hR : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list (A ++ B)) acc rt cb₂ = .ok R)
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list A) accA rt cb₁ =
      .ok (.tuple #[g, Term.list V, Term.list Mi, a]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list B) accB rt cb₁ = .ok Y) :
    GShift g V Mi R Y := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at hR hA hB
  rw [foldl_fun, foldl1_list_append] at hR
  obtain ⟨X, hX, hR'⟩ := bind_ok hR
  rw [← foldl_fun] at hX hR'
  obtain ⟨g', V', Mi', a', b', eA, hx, -⟩ := gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm _ (gshift_fresh acc accA) hX hA
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eA
  obtain ⟨e₁, eV, eM, -⟩ := eA
  rw [← e₁, ← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] at hR' <;> simp only [List.append_nil] at hR' <;>
    exact gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm _ (gshift_start _ V Mi a' accB) hR' hB

theorem orElse_boolT {g g' : Term} (hg : g = .atom "true" ∨ g = .atom "false")
    (hg' : g' = .atom "true" ∨ g' = .atom "false") :
    ∃ F, Lynx.Except.orElse (.ok g) (.ok g') true = .ok F ∧ (F = .atom "true" ∨ F = .atom "false") := by
  rcases hg with rfl | rfl
  · exact ⟨_, rfl, Or.inl rfl⟩
  · exact ⟨g', by simp [Lynx.Except.orElse], hg'⟩

@[simp] theorem orElse_true_l (x : Except Exception Term) : Lynx.Except.orElse (.ok (.atom "true")) x true = .ok (.atom "true") := rfl

@[simp] theorem orElse_false_l (x : Except Exception Term) : Lynx.Except.orElse (.ok (.atom "false")) x true = x := by
  simp [Lynx.Except.orElse]

theorem minus_nil (l : List Term) : Erlang.erlang.«--/2» .nil (Term.list l) = .ok .nil := by
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have pn : Term.properList? .nil = some [] := Term.properList?_list []
  simp [Erlang.erlang.«--/2», Term.properList?_list, pn, e00]

theorem minus_nil0 : Erlang.erlang.«--/2» .nil .nil = .ok .nil := minus_nil []

theorem app_nil_l (l : List Term) : Erlang.erlang.«++/2» .nil (Term.list l) = .ok (Term.list l) := append_list [] l

theorem app_nil0 : Erlang.erlang.«++/2» .nil .nil = .ok .nil := append_list [] []

theorem app_nil_r (l : List Term) : Erlang.erlang.«++/2» (Term.list l) .nil = .ok (Term.list l) := by
  simpa using append_list l []

theorem dnf_opt_relB_force (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "force"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Dr ++ Do)) (.tuple #[c, .atom "force"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, app_nil_r, append_list, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ hcb Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem dnf_opt_relB_keep (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Dr ++ Do)) (.tuple #[c, .atom "keep"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, app_nil_r, append_list, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ hcb Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem dnf_opt_relB_reject (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Do ++ Dr)) (.tuple #[c, .atom "reject"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ :=
    gd_append_rel2 (m + 1) dnf (.map []) a₁ (.map []) (.atom "true") _ _ hcb Do Dr hH hG' hG
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, eV, eM, rfl⟩ := eY
  rw [← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁' with h | h <;> (try subst h) <;>
      simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind, Lynx.Except.orElse,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all
  all_goals sorry

theorem dnf_opt_relB (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (md : String) (hmd : Mode md)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom md])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (if md = "reject" then Do ++ Dr else Dr ++ Do)) (.tuple #[c, .atom md])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  rcases hmd with rfl | rfl | rfl
  · exact dnf_opt_relB_force m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂
  · exact dnf_opt_relB_keep m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂
  · exact dnf_opt_relB_reject m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂

theorem dnf_neg_relB_keep (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Dr ++ Do), .nil]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, app_nil_r, append_list, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ rfl Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


theorem dnf_neg_relB_force (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "force"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Dr ++ Do), .nil]) (.tuple #[c, .atom "force"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso, app_nil_r, append_list, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ rfl Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


theorem dnf_neg_relB_reject (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Do ++ Dr), .nil]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ :=
    gd_append_rel2 (m + 1) dnf (.map []) a₁ (.map []) (.atom "true") _ _ rfl Do Dr hH hG' hG
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, eV, eM, rfl⟩ := eY
  rw [← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁' with h | h <;> (try subst h) <;>
      simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.orElse] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


/-! Splits of gradual keys with required atoms and a negated set holding them: the updates at the atoms outside
the set and at the required atoms. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The named keys of a split with required atoms inside a negated set: the required atoms updated, and the keys
outside the set read. -/
theorem named_tail_negA (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (hne : lines ≠ []) (A ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : List Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, Term.list errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (keepOp v keep) (.atom "false") (.atom "true") (.atom "true")
        (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w := by
  classical
  let lk : String → Bool := fun a => decide (Lacking den lines a)
  have hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a := fun a => by simp [lk]
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, -, -, -, bT₂⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.true Bool.true lk hlk A Bl fl T₁ (Term.list errs) hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, -, -, -, bF', -⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.false Bool.false lk hlk ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  refine ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => ?_⟩
  rw [sB₂]
  exact or_congr_right (exists_congr fun a => and_congr_right fun _ => keepSem_iff)

end

/-- List difference of atoms keeps the first list when no atom of the second is in it. -/
theorem minus_disj (ks A : List String) (h : ∀ s ∈ ks, s ∉ A) :
    Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) (Term.list (A.map Term.atom)) =
      .ok (Term.list (ks.map Term.atom)) := by
  have keep : ∀ (B : List String), (∀ s ∈ ks, s ∉ B) →
      List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
        (ks.map Term.atom) (B.map Term.atom) = ks.map Term.atom := by
    intro B hB
    induction B with
    | nil => rfl
    | cons b B ih =>
      simp only [List.map_cons, List.foldl_cons]
      have e : List.eraseP (fun x => decide (compareExact (x.fuel (.atom b)) x (.atom b) = .eq)) (ks.map Term.atom) =
          ks.map Term.atom := by
        apply List.eraseP_of_forall_not
        intro x mx
        obtain ⟨s, ms, rfl⟩ := List.mem_map.mp mx
        simp only [decide_eq_true_eq, compareExact_eq_atom, Term.atom.injEq]
        intro e; subst e; exact hB s ms List.mem_cons_self
      rw [e]
      exact ih fun s ms m => hB s ms (List.mem_cons_of_mem _ m)
  simp [Erlang.erlang.«--/2», Term.properList?_list, keep A h]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem upd_dnf_negreq (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (A : List String) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.map N) (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm v keep w ∨
          ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w) := by
  classical
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have mk0 : Erlang.erlang.«++/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using append_list (ks.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  have minusKA := minus_disj ks A fun s ms ma => hA s ma (hks s ms)
  have minusK0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using minus_disj ks [] (by simp)
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ ks)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3»]
    simpa [append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  cases keep
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      modeT, r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨-, NK, -, -, -, -, -, lnNK, -⟩ := box_named (E := E) (n + 1) lines hl' AK
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, (kind_held ef hl hne lnNK (hDs d ms)).mpr h⟩
      · rintro ⟨ms, h⟩
        exact ⟨d, ms, rfl, (kind_held ef hl hne lnNK (hDs d ms)).mp h⟩
    have noAtom : "atom" ∉ Ks → ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x := fun na L mL x hx =>
      na ((memKs _).mpr ⟨hat, (kind_held ef hl hne lnNK (hDs _ hat)).mpr ⟨L, mL, x, hx⟩⟩)
    have rmode : keepOp v Bool.false = cOp v Bool.false "reject" := keepOp_cOp v Bool.false
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      have part := partition_atom (n + 5) []
      simp only [List.map_nil, List.filter_nil] at part
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
        (mode_modeS Bool.false) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' [] (by simp)
        (Or.inr ⟨rfl, noAtom (by simp)⟩)
        ⟨fun h => by simp at h, fun h => by simpa using h "atom" (by simp [domainKinds])⟩
      replace rX : Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) .nil (keepOp v Bool.false) (Term.list (AK.map Term.atom)) = .ok (.map X) := by
        rw [rmode]; exact rX
      simp [Term.list, boolAtom, Lynx.Except.orElse,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.false)
          [] w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemKR, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl hne
          A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl hne
          A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        have mapE : Term.map X ≠ Term.map [] := fun e => neX (by injection e)
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
        simpa using length_list (Ks.map Term.atom)
      have fullI : Ks.length = 12 ↔ FullK Ks := by
        rw [lenKs]
        exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
      have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
          (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.false)
            Bx w) →
          (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v (modeS Bool.false) Ws w) →
          ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
          ∀ w, (SB w ∨ SW w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w := by
        intro Bx Ws SB SW hB hW hc w
        rw [hB, hW]
        rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
        · simp [UpdSemKR, hf]
        · simp [UpdSemKR, hf]
      -- The descr: the box, and the widened kinds.
      have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
          (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
          ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
            (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (keepOp v Bool.false)
            (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
          MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
            (modeS Bool.false) Bx) := by
        intro Bx sub hf hnf
        have hAt : "atom" ∈ Bx ∨ (modeS Bool.false = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
          by_cases ak : "atom" ∈ Ks
          · left
            by_cases full : FullK Ks
            · rw [hf full]; exact ak
            · rw [hnf full]; simp [ak]
          · exact Or.inr ⟨rfl, noAtom ak⟩
        have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
          by_cases full : FullK Ks
          · rw [hf full, fullI]; exact Iff.rfl
          · rw [hnf full]
            constructor
            · intro h
              have : (Ks.filter (· = "atom")).length ≤ 1 := by
                have nd := ndKs.filter (fun x => decide (x = "atom"))
                have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                  simpa using (List.mem_filter.mp m).2
                generalize Ks.filter (· = "atom") = l at nd all
                match l, nd, all with
                | [], _, _ => simp
                | [_], _, _ => simp
                | x :: y :: t, nd, all =>
                  exfalso
                  have ex := all x List.mem_cons_self
                  have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                  exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
              omega
            · intro h
              have := h "binary" (by simp [domainKinds])
              simp at this
        obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
          (mode_modeS Bool.false) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
          (fun d md => subKs d (sub d md)) hAt hlen
        refine ⟨X, ?_, mX⟩
        rw [rmode]; exact rX
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, Erlang.erlang.«element/2», modeT, lenK,
        Lynx.Term.compare_integers]
      by_cases full : FullK Ks
      · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
        obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
            (modeS Bool.false) Ks w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v
            Bool.false w := fun w => by
          have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
          simpa using this
        simp [hL', rZ, Term.list]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
            hne A ks [] (by simp) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
            hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]

      · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
        have part := partition_atom (n + 5) Ks
        obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
          (fun h => absurd h full) (fun _ => rfl)
        have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
        have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
        simp [hL', part, rX]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          have MZ := mX
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
              (modeS Bool.false) (Ks.filter (· = "atom")) w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks v Bool.false w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


        · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) hv Bool.false (Or.inr vne) (mode_modeS Bool.false)
            (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
          rw [← keepOp_cOp] at rW
          obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp at wsCmp rW
          simp [wsCmp, rW, rZ]
          have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
              (modeS Bool.false) (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v
              (modeS Bool.false) (Ks.filter (· ≠ "atom")) w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks v Bool.false w := fun w =>
            semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
              (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      modeT, r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ (Bool.true = Bool.true ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memK0 d
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have full : ¬(Bool.true = Bool.false ∧ FullK Ks) := fun h => by cases h.1
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.true)
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v (modeS Bool.true) Ws w) →
        Bx = Ks.filter (· = "atom") → Ws = Ks.filter (· ≠ "atom") →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w := by
      intro Bx Ws SB SW hB hW eB eW w
      subst eB eW
      rw [hB, hW]
      simp [UpdSemKR]
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have part := partition_atom (n + 5) Ks
    have rmode : keepOp v Bool.true = cOp v Bool.false "keep" := keepOp_cOp v Bool.true
    obtain ⟨X, rX, mX⟩ : ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list ((Ks.filter (· = "atom")).map Term.atom)) (keepOp v Bool.true)
        (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom"))) := by
      have hlen : (Ks.filter (· = "atom")).length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ks.filter (· = "atom") := by
        constructor
        · intro h
          have : (Ks.filter (· = "atom")).length ≤ 1 := by
            have nd := ndKs.filter (fun x => decide (x = "atom"))
            have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
              simpa using (List.mem_filter.mp m).2
            generalize Ks.filter (· = "atom") = l at nd all
            match l, nd, all with
            | [], _, _ => simp
            | [_], _, _ => simp
            | x :: y :: t, nd, all =>
              exfalso
              have ex := all x List.mem_cons_self
              have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
              exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
          omega
        · intro h
          have := h "binary" (by simp [domainKinds])
          simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
        (mode_modeS Bool.true) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' (Ks.filter (· = "atom"))
        (fun d m => subKs d (List.mem_filter.mp m).1) (Or.inl (by simp [aK])) hlen
      refine ⟨X, ?_, mX⟩
      rw [rmode]; exact rX
    have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
    have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    simp [dne', rKs, Erlang.erlang.«element/2», modeT, part, rX, o1, o2]
    by_cases wn : Ks.filter (· ≠ "atom") = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
      simp [wn', Term.list]
      have MZ := mX
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom")) w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks v Bool.true w := fun w => by
        have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
          (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) rfl rfl w
        simpa using this
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


    · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) hv Bool.false (Or.inr vne) (mode_modeS Bool.true)
        (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
      rw [← keepOp_cOp] at rW
      obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
      have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
        cases h : Ks.filter (· ≠ "atom") with
        | nil => exact absurd h wn
        | cons d ds => simp [Term.list]
      simp at wsCmp rW
      simp [wsCmp, rW, rZ]
      have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v
          (modeS Bool.true) (Ks.filter (· ≠ "atom")) w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks v Bool.true w := fun w =>
        semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
          (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) rfl rfl w
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]




end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem named_tail_negA_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (A ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "false") (.atom "true")
        (.atom "true") (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w := by
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, bT₂⟩ := named_del (st := Bool.true) ef (n := n + 2) (by omega) hmd lines hl Bool.true Bool.true
    A Bl fl T₁ errs hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, bF', -⟩ := named_del (st := Bool.true) ef (n := n + 2) (by omega) hmd lines hl Bool.false Bool.false
    ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  exact ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => by rw [sB₂]⟩


theorem upd_dnf_negreq_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (A : List String) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.map N) (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm md w ∨
          ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  classical
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have mk0 : Erlang.erlang.«++/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using append_list (ks.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  have minusKA := minus_disj ks A fun s ms ma => hA s ma (hks s ms)
  have minusK0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using minus_disj ks [] (by simp)
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ ks)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3»]
    simpa [append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  rcases hmd with rfl | rfl | rfl
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR', Lynx.Except.andAlso]
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
      simpa using length_list (Ks.map Term.atom)
    have fullI : Ks.length = 12 ↔ FullK Ks := by
      rw [lenKs]
      exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "force"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "force" Ws w) →
        ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := by
      intro Bx Ws SB SW hB hW hc w
      rw [hB, hW]
      rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · simp [UpdSemD, hf]
      · simp [UpdSemD, hf]
    -- The descr: the box, and the widened kinds.
    have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
        (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
        ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "force")
          (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Bx) := by
      intro Bx sub hf hnf
      have hAt : "atom" ∈ Bx ∨ ("force" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
        by_cases ak : "atom" ∈ Ks
        · left
          by_cases full : FullK Ks
          · rw [hf full]; exact ak
          · rw [hnf full]; simp [ak]
        · exact absurd aK ak
      have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
        by_cases full : FullK Ks
        · rw [hf full, fullI]; exact Iff.rfl
        · rw [hnf full]
          constructor
          · intro h
            have : (Ks.filter (· = "atom")).length ≤ 1 := by
              have nd := ndKs.filter (fun x => decide (x = "atom"))
              have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                simpa using (List.mem_filter.mp m).2
              generalize Ks.filter (· = "atom") = l at nd all
              match l, nd, all with
              | [], _, _ => simp
              | [_], _, _ => simp
              | x :: y :: t, nd, all =>
                exfalso
                have ex := all x List.mem_cons_self
                have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
            omega
          · intro h
            have := h "binary" (by simp [domainKinds])
            simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inl rfl) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
        (fun d md => subKs d (sub d md)) hAt hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    simp [dne', o1, o2, rKs, Erlang.erlang.«element/2», lenK,
      Lynx.Term.compare_integers]
    by_cases full : FullK Ks
    · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
      obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := fun w => by
        have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
        simpa using this
      simp [hL', rZ, Term.list]
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
          A ks [] (by simp) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
          A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]

    · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
      have part := partition_atom (n + 5) Ks
      obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
        (fun h => absurd h full) (fun _ => rfl)
      have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
      have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      simp [hL', part, rX]
      by_cases wn : Ks.filter (· ≠ "atom") = []
      · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
        simp [wn', Term.list]
        have MZ := mX
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w => by
          have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
            (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          simpa using this
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]


      · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inl rfl)
          (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
        obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
        have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
          cases h : Ks.filter (· ≠ "atom") with
          | nil => exact absurd h wn
          | cons d ds => simp [Term.list]
        simp at wsCmp rW
        simp [wsCmp, rW, rZ]
        have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
            "force" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w =>
          semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
            (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ ("keep" ≠ "reject" ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memK0 d
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have full : ¬("keep" ≠ "keep" ∧ FullK Ks) := fun h => h.1 rfl
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "keep"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "keep" Ws w) →
        Bx = Ks.filter (· = "atom") → Ws = Ks.filter (· ≠ "atom") →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w := by
      intro Bx Ws SB SW hB hW eB eW w
      subst eB eW
      rw [hB, hW]
      simp [UpdSemD]
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have part := partition_atom (n + 5) Ks
    obtain ⟨X, rX, mX⟩ : ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list ((Ks.filter (· = "atom")).map Term.atom)) (cOp (.map []) Bool.true "keep")
        (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom"))) := by
      have hlen : (Ks.filter (· = "atom")).length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ks.filter (· = "atom") := by
        constructor
        · intro h
          have : (Ks.filter (· = "atom")).length ≤ 1 := by
            have nd := ndKs.filter (fun x => decide (x = "atom"))
            have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
              simpa using (List.mem_filter.mp m).2
            generalize Ks.filter (· = "atom") = l at nd all
            match l, nd, all with
            | [], _, _ => simp
            | [_], _, _ => simp
            | x :: y :: t, nd, all =>
              exfalso
              have ex := all x List.mem_cons_self
              have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
              exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
          omega
        · intro h
          have := h "binary" (by simp [domainKinds])
          simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inl rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' (Ks.filter (· = "atom"))
        (fun d m => subKs d (List.mem_filter.mp m).1) (Or.inl (by simp [aK])) hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
    have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    simp [dne', rKs, Erlang.erlang.«element/2», part, rX, o1, o2]
    by_cases wn : Ks.filter (· ≠ "atom") = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
      simp [wn', Term.list]
      have MZ := mX
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w => by
        have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
          (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) rfl rfl w
        simpa using this
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


    · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
      obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
      have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
        cases h : Ks.filter (· ≠ "atom") with
        | nil => exact absurd h wn
        | cons d ds => simp [Term.list]
      simp at wsCmp rW
      simp [wsCmp, rW, rZ]
      have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
          "keep" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w =>
        semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
          (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) rfl rfl w
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨-, NK, -, -, -, -, -, lnNK, -⟩ := box_named (E := E) (n + 1) lines hl' AK
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, (kind_held ef hl hne lnNK (hDs d ms)).mpr h⟩
      · rintro ⟨ms, h⟩
        exact ⟨d, ms, rfl, (kind_held ef hl hne lnNK (hDs d ms)).mp h⟩
    have noAtom : "atom" ∉ Ks → ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x := fun na L mL x hx =>
      na ((memKs _).mpr ⟨hat, (kind_held ef hl hne lnNK (hDs _ hat)).mpr ⟨L, mL, x, hx⟩⟩)
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      have part := partition_atom (n + 5) []
      simp only [List.map_nil, List.filter_nil] at part
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' [] (by simp)
        (Or.inr ⟨rfl, noAtom (by simp)⟩)
        ⟨fun h => by simp at h, fun h => by simpa using h "atom" (by simp [domainKinds])⟩
      replace rX : Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) .nil (cOp (.map []) Bool.true "reject") (Term.list (AK.map Term.atom)) = .ok (.map X) := by
        exact rX
      simp [Term.list, boolAtom, Lynx.Except.orElse,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
          [] w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemD, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        have mapE : Term.map X ≠ Term.map [] := fun e => neX (by injection e)
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
        simpa using length_list (Ks.map Term.atom)
      have fullI : Ks.length = 12 ↔ FullK Ks := by
        rw [lenKs]
        exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
      have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
          (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
            Bx w) →
          (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "reject" Ws w) →
          ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
          ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := by
        intro Bx Ws SB SW hB hW hc w
        rw [hB, hW]
        rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
        · simp [UpdSemD, hf]
        · simp [UpdSemD, hf]
      -- The descr: the box, and the widened kinds.
      have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
          (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
          ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
            (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "reject")
            (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
          MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Bx) := by
        intro Bx sub hf hnf
        have hAt : "atom" ∈ Bx ∨ ("reject" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
          by_cases ak : "atom" ∈ Ks
          · left
            by_cases full : FullK Ks
            · rw [hf full]; exact ak
            · rw [hnf full]; simp [ak]
          · exact Or.inr ⟨rfl, noAtom ak⟩
        have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
          by_cases full : FullK Ks
          · rw [hf full, fullI]; exact Iff.rfl
          · rw [hnf full]
            constructor
            · intro h
              have : (Ks.filter (· = "atom")).length ≤ 1 := by
                have nd := ndKs.filter (fun x => decide (x = "atom"))
                have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                  simpa using (List.mem_filter.mp m).2
                generalize Ks.filter (· = "atom") = l at nd all
                match l, nd, all with
                | [], _, _ => simp
                | [_], _, _ => simp
                | x :: y :: t, nd, all =>
                  exfalso
                  have ex := all x List.mem_cons_self
                  have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                  exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
              omega
            · intro h
              have := h "binary" (by simp [domainKinds])
              simp at this
        obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
          (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
          (fun d md => subKs d (sub d md)) hAt hlen
        refine ⟨X, ?_, mX⟩
        exact rX
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, Erlang.erlang.«element/2», lenK,
        Lynx.Term.compare_integers]
      by_cases full : FullK Ks
      · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
        obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := fun w => by
          have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
          simpa using this
        simp [hL', rZ, Term.list]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]

      · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
        have part := partition_atom (n + 5) Ks
        obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
          (fun h => absurd h full) (fun _ => rfl)
        have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
        have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
        simp [hL', part, rX]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          have MZ := mX
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


        · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inr rfl))
            (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
          obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp at wsCmp rW
          simp [wsCmp, rW, rZ]
          have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
              "reject" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w =>
            semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
              (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem kr_update_static_req (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) {A Ds : List String} {neg : Term} {N : List (Term × Term)} (eN : neg = .map N)
    (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (A.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (fun w => UpdSemKR den (fun u => denMF E den b u = Bool.true) [] neg Dm v keep w ∨
              ∃ a ∈ A, KeepSemM den (fun u => denMF E den b u = Bool.true) v keep a w)) := by
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
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq ef hn hv sv vne keep (.tuple #[.integer k, tag, fieldsTerm l]) fb _ hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
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
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq ef hn hv sv vne keep b fb (L :: rest) hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
      rw [conv inB] at hY mDm
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

theorem del_update_static_req (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    {A Ds : List String} {neg : Term} {N : List (Term × Term)} (eN : neg = .map N)
    (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (A.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (fun w => UpdSemD den (fun u => denMF E den b u = Bool.true) [] neg Dm md w ∨
              ∃ a ∈ A, DelAt (fun u => denMF E den b u = Bool.true) md a w)) := by
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
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq_del ef hn hmd (.tuple #[.integer k, tag, fieldsTerm l]) fb _ hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
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
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq_del ef hn hmd b fb (L :: rest) hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
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


/-! Forced updates build the same maps whether they return the old values or not. -/

/-- `map_update_named_key/5` builds the same maps whether it reads the old values or not. -/
theorem named_key_ov (d : Dispatcher) (dnf key op bld ov₁ ov₂ : Term) {t₁ t₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov₁ = .ok t₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov₂ = .ok t₂) :
    ∃ bds o₁ o₂, t₁ = .tuple #[bds, o₁] ∧ t₂ = .tuple #[bds, o₂] := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5» at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals (repeat' split at h₁) <;> (try (cases h₁; done))
  all_goals (repeat' split at h₂) <;> (try (simp at h₂; done))
  all_goals (try (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂))
  all_goals first
    | exact ⟨_, _, _, rfl, rfl⟩
    | trace_state

theorem named_step_relB2 (d : Dispatcher) (dnf op req₁ req₂ s₁ s₂ bld ov₁ ov₂ fo key : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₁ s₁ bld ov₁ fo key a = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₂ s₂ bld ov₂ fo key b = .ok r₂) :
    RelB r₁ r₂ := by
  obtain ⟨v₁, bd, e₁, f₁, v₂, e₂, f₂, rfl, rfl⟩ := hab
  obtain ⟨bds, old, B, k₁, b₁, a, e, f, rfl⟩ := named_step_maps d dnf op req₁ s₁ bld ov₁ fo key h₁
  obtain ⟨bds', old', B', k₂, b₂, a', e', f', rfl⟩ := named_step_maps d dnf op req₂ s₂ bld ov₂ fo key h₂
  obtain ⟨c, o₁, o₂, e₁', e₂'⟩ := named_key_ov d dnf key op bld ov₁ ov₂ k₁ k₂
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e₁' e₂'
  obtain ⟨rfl, -⟩ := e₁'
  obtain ⟨rfl, -⟩ := e₂'
  rw [b₁] at b₂; cases b₂
  exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩

/-- `map_update_named_keys/8` gives the same maps whatever the keys' requirement, the static flag, and whether it reads
the old values. -/
theorem named_keys_relB2 (m : Nat) (dnf keys op bo req₁ req₂ s₁ s₂ rt₁ rt₂ : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req₁ s₁ rt₁ bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req₂ s₂ rt₂ bo = .ok r₂) :
    RelB r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals (split at h₁ <;> (try (cases h₁; done)))
  all_goals (split at h₂ <;> (try (simp at h₂; done)))
  all_goals
    refine foldl_relP RelB _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    exact named_step_relB2 _ _ _ _ _ _ _ _ _ _ _ _ hab e₁ e₂

theorem dnf_rt_relB_force (m : Nat) (bdd dnf Rk Ok neg Rd Od c st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rk, Ok, neg, Rd, Od]) (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rk, Ok, neg, Rd, Od]) (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) : RelB r₁ r₂ := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the domains.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Rd (.map [])
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) =
      .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Rd (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Od a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) =
      .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Od a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  obtain ⟨Dm, hDm⟩ : ∃ Dm, Erlang.erlang.«++/2» Rd Od = .ok Dm := by
    cases h : Erlang.erlang.«++/2» Rd Od with
    | error e => simp [h] at h₂
    | ok Dm => exact ⟨Dm, rfl⟩
  simp only [hDm] at h₁ h₂
  obtain ⟨F, hF, bF⟩ := orElse_boolT hg₁ hg₁'
  simp only [hF] at h₁
  have oT : Lynx.Except.orElse (.ok F) (.ok (.atom "true")) true = .ok (.atom "true") := by
    rcases bF with rfl | rfl <;> rfl
  simp only [oT] at h₁ h₂
  all_goals
    try simp only [
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
    -- The found flags differ, but only end in the accumulators.
    split at h₁ <;> (try (cases h₁; done))
    split at h₂ <;> (try (simp at h₂; done))
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB2 (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB2 (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem static_rt_rel_ne (m : Nat) (descr Rk Ok neg Rd Od c st₁ st₂ : Term) (hd : descr ≠ .atom "term") {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (dnf_rt_relB_force _ _ _ _ _ _ _ _ _ _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)
    | trace_state

/-- Forcing, `map_update_static/5` gives the same maps whether it returns the old values or not. -/
theorem static_rt_rel (m : Nat) (descr Rk Ok neg Rd Od c st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_rt_rel_ne m _ _ _ _ _ _ _ _ _ (by simp) h₁ h₂
  · exact static_rt_rel_ne m descr _ _ _ _ _ _ _ _ h h₁ h₂


/-! The shapes of the splits of keys. -/

section
variable {V : Type}

/-- Splits of keys `map_update_static_dnf/6` reads like static ones: without a negated set, the required and optional
atoms and domains; with one and without atoms, the domains; or required atoms inside a negated set; with the keys
`KP`. -/
def GForm (s : Term) (KP : MKey → Prop) : Prop :=
  (∃ Rs Os Ds Ds' : List Term, s = .tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Ds, Term.list Ds'] ∧
    SplitOk (Rs ++ Os) (.atom "nil") (Ds ++ Ds') ∧ ∀ κ, SplitKey (Rs ++ Os) (.atom "nil") (Ds ++ Ds') κ ↔ KP κ) ∨
  (∃ (N : List (Term × Term)) (Ds Ds' : List Term), s = .tuple #[.nil, .nil, .map N, Term.list Ds, Term.list Ds'] ∧
    SplitOk [] (.map N) (Ds ++ Ds') ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
    ∀ κ, SplitKey [] (.map N) (Ds ++ Ds') κ ↔ KP κ) ∨
  (∃ (A : List String) (N : List (Term × Term)) (Ds Ds' : List Term),
    s = .tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list Ds, Term.list Ds'] ∧
    SplitOk [] (.map N) (Ds ++ Ds') ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
    (∀ a ∈ A, mapLookup N (.atom a) ≠ none) ∧
    ∀ κ, ((∃ a ∈ A, κ = .atom a) ∨ SplitKey [] (.map N) (Ds ++ Ds') κ) ↔ KP κ)

end

section
variable {t : Term} {n : Nat}

theorem gsplit_form {X : List (Term × Term)} {Dy : Term} (gk : GC (level t n) (.map X))
    (hD : mapLookup X (.atom "dynamic") = some Dy)
    (aS : ∀ tag S, mapLookup X (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    (aD : ∀ Y, Dy = .map Y → ∀ tag S, mapLookup Y (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map X) = .ok s ∧
      GForm s (KeyPt t n Dy) := by
  obtain ⟨tD, dS, incl⟩ : TC (level t n) Dy ∧ DE (level t n).E (.map (rmDyn X)) ∧
      ∀ q : TP (level t n), denD (.map X) q → denD Dy q := by
    rcases gk with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
    · rcases tX with h | ⟨X', e, sX'⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e
      rw [hD] at hD'; cases hD'
      exact ⟨tD, Or.inr ⟨_, rfl, dS⟩, incl⟩
  obtain ⟨Yd, dds, unf, dY, semY, rdd, hdds, hdat, hdk, aY⟩ := dyn_info tD aD hm
  obtain ⟨rds, rrd, hrds, hrat, hrk⟩ := dom_kinds dS hm
  have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
  obtain ⟨odds, rod, sod, ind⟩ := diff_atoms dds rds fun x mx => let ⟨s, _, e⟩ := hdds x mx; ⟨s, e⟩
  have rem : Erlang.maps.«remove/2» (.atom "dynamic") (.map X) = .ok (.map (rmDyn X)) := by
    simp [Erlang.maps.«remove/2», rmDyn]
  -- Atoms and kinds of the static part are those of the dynamic part.
  have inclA : ∀ s, amemV (mapLookup X (.atom "atom")) (.atom s) = Bool.true →
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s h =>
    (denD_aPt (t := t) (n := n) (Y := Yd) _).mp ((semY _).mp (incl _ ((denD_aPt (t := t) (n := n) (Y := X) _).mpr h)))
  have keyA : ∀ s, KeyPt t n Dy (.atom s) ↔ amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s =>
    (semY _).trans (denD_aPt _)
  have inclK : ∀ k, Term.atom (domKind k) ∈ rds → Term.atom (domKind k) ∈ dds := fun k h => by
    obtain ⟨v, hv, pv⟩ := (hrk _ (domKind_ne_atom k)).mp h
    exact (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp (incl v ((denD_rmDyn X v).mp hv)), pv⟩
  have dsK : ∀ k i, Term.atom (domKind k) ∈ rds ++ odds ↔ KeyPt t n Dy (.dom k i) := fun k i => by
    have : KeyPt t n Dy (.dom k i) ↔ Term.atom (domKind k) ∈ dds :=
      ⟨fun ⟨v, hv, pv⟩ => (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp hv, pv⟩, fun h =>
        let ⟨v, hv, pv⟩ := (hdk _ (domKind_ne_atom k)).mp h; ⟨v, (semY v).mpr hv, pv⟩⟩
    rw [this, List.mem_append]
    constructor
    · rintro (h | h)
      · exact inclK k h
      · exact sod _ h
    · intro h
      by_cases r : Term.atom (domKind k) ∈ rds
      · exact Or.inl r
      · exact Or.inr (ind _ h r)
  have hds : ∀ d ∈ rds ++ odds, ∃ s ∈ domainKinds, d = .atom s := fun d md =>
    (List.mem_append.mp md).elim (hrds d) fun h => hdds d (sod d h)
  have datom : Term.atom "atom" ∈ rds ++ odds ↔ Term.atom "atom" ∈ rds ∨ Term.atom "atom" ∈ dds := by
    rw [List.mem_append]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (sod _ h)
    · rintro (h | h)
      · exact Or.inl h
      · by_cases r : Term.atom "atom" ∈ rds
        · exact Or.inl r
        · exact Or.inr (ind _ h r)
  -- Splits with the domains of the dynamic part.
  have single : ∀ rs neg, (∀ s, SplitKey rs neg (rds ++ odds) (.atom s) ↔
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true) →
      ∀ κ, (∃ sp ∈ [(rs, neg, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
    intro rs neg h κ
    simp only [List.mem_singleton, exists_eq_left]
    cases κ with
    | atom s => exact (h s).trans (keyA s).symm
    | dom k i => exact dsK k i
  -- The shapes of the atoms.
  have shapeX : mapLookup X (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup X (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup X (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dS).fields _ _ (lX.trans h))
      exact Or.inr ⟨pos, S, aS _ S h (by cases pos <;> simp), rfl⟩
  have shapeY : mapLookup Yd (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup Yd (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup Yd (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dY).fields _ _ h)
      exact Or.inr ⟨pos, S, aY _ S h (by cases pos <;> simp), rfl⟩
  have noRat : mapLookup X (.atom "atom") = none ∨ (∃ S, mapLookup X (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ rds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
  have noDat : mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ dds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
  have aDs : ∀ d ∈ rds ++ odds, d = .atom "atom" → mapLookup X (.atom "atom") = none ∨
      (∃ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S])) →
      mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
        some (.tuple #[.atom "union", .map S])) → False := by
    rintro d md rfl hx hy
    rcases datom.mp md with h | h
    · exact noRat hx h
    · exact noDat hy h
  -- Splits without a negated set, or with one, and their domains.
  have okNil : ∀ rs : List Term, (∀ r ∈ rs, ∃ s, r = .atom s) → Term.atom "atom" ∉ rds ++ odds →
      ∀ sp ∈ [(rs, Term.atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro rs hrs na sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨hrs, Or.inl rfl, hds, ⟨fun h => absurd h na, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
  have okNeg : ∀ N, Term.atom "atom" ∈ rds ++ odds →
      ∀ sp ∈ [([], Term.map N, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro N ha sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨by simp, Or.inr ⟨N, rfl⟩, hds, ⟨fun _ => ⟨N, rfl⟩, fun _ => ha⟩⟩, fun _ _ => rfl⟩
  have atomsOf : ∀ A : List String, ∀ r ∈ A.map Term.atom, ∃ s, r = .atom s := fun A r mr => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩
  have memA : ∀ (A : List String) (s : String), Term.atom s ∈ A.map Term.atom ↔ s ∈ A := fun A s => by simp
  rcases shapeX with hx | ⟨px, S, aSS, hx⟩ <;> rcases shapeY with hy | ⟨py, Dn, aDD, hy⟩
  · -- No atoms.
    have na : Term.atom "atom" ∉ rds ++ odds := fun m => (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inl hy))
    have hk : ∀ κ, (∃ sp ∈ [([] ++ [], .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
        refine single _ _ fun s => ?_
        simp [SplitKey, hy, amemV]
    refine ⟨.tuple #[.nil, .nil, .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨[], [], rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      rcases unf with ⟨rfl, ut⟩ | rfl
      · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
      · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
    · have hok : ∀ sp ∈ [([] ++ [], .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
        exact okNil _ (by simp) na
      simpa using (hok _ List.mem_cons_self).1
  · cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · -- Atoms outside a dynamic negated set.
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([], .map Dn, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp [SplitKey, hy, amemV]
      refine ⟨.tuple #[.nil, .nil, .map Dn, Term.list rds, Term.list odds], ?_, Or.inr (Or.inl ⟨Dn, rds, odds, rfl, ?_, ?_, fun κ => by simpa using hk κ⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
      · have hok : ∀ sp ∈ [([], .map Dn, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNeg Dn ha
        simpa using (hok _ List.mem_cons_self).1
      · have hna : ∀ N', Term.map Dn = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aDD
        exact hna _ rfl
    · -- Dynamic atoms, optional.
      obtain ⟨Dl, rDl, mDl⟩ := aset_list aDD (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([] ++ Dl.map Term.atom, .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp [SplitKey, hy, amemV, mDl]
      refine ⟨.tuple #[.nil, Term.list (Dl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨[], Dl.map Term.atom, rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rDl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rDl]
      · have hok : ∀ sp ∈ [([] ++ Dl.map Term.atom, .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ (by simp) na
        simpa using (hok _ List.mem_cons_self).1
  · cases px <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx
    · -- A static negated set without dynamic atoms: impossible, as some atom outside it would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      have := inclA c (by simp [hx, amemV, lookup_fresh' hc])
      simp [hy, amemV] at this
    · -- Static atoms without dynamic atoms: none, as they would be dynamic.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inl hy))
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom ++ [], .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp only [SplitKey, List.append_nil, memA, mSl, hy, amemV]
          constructor
          · rintro (h | ⟨N, e, -⟩)
            · have := inclA s (by simpa [hx, amemV] using h)
              simp [hy, amemV] at this
            · cases e
          · intro h; cases h
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨Sl.map Term.atom, [], rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom ++ [], .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ (by simp) na
        simpa using (hok _ List.mem_cons_self).1
  · cases px <;> cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    · -- Both negated: the atoms outside both sets.
      obtain ⟨R, rR, aR, mR⟩ := aset_inter aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([], .map R, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          have i := inclA s
          simp only [hx, hy, amemV, Bool.not_eq_true'] at i
          simp only [SplitKey, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
          constructor
          · rintro ⟨N, e, h⟩
            cases e
            have := mR (.atom s)
            rw [h] at this
            cases hd : (mapLookup Dn (.atom s)).isSome
            · rfl
            · cases hs : (mapLookup S (.atom s)).isSome
              · have := i (by simpa using hs); simp [hd] at this
              · simp [hd, hs] at this
          · intro h
            refine ⟨R, rfl, ?_⟩
            have := mR (.atom s)
            cases hR : mapLookup R (.atom s)
            · rfl
            · rw [hR] at this; simp [h] at this
      refine ⟨.tuple #[.nil, .nil, .map R, Term.list rds, Term.list odds], ?_, Or.inr (Or.inl ⟨R, rds, odds, rfl, ?_, ?_, fun κ => by simpa using hk κ⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rR]
      · have hok : ∀ sp ∈ [([], .map R, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNeg R ha
        simpa using (hok _ List.mem_cons_self).1
      · have hna : ∀ N', Term.map R = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aR
        exact hna _ rfl
    · -- A static negated set with dynamic atoms: impossible, as some atom outside both would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S ++ keyStrs Dn)
      have := inclA c (by simp [hx, amemV, lookup_fresh' (fun m => hc (List.mem_append_left _ m))])
      simp [hy, amemV, lookup_fresh' (fun m => hc (List.mem_append_right _ m))] at this
    · -- Static atoms and a dynamic negated set: the static atoms, and the atoms outside both.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_union aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hA : ∀ a ∈ Sl, mapLookup R (.atom a) ≠ none := fun a ma => by
        have := mR (.atom a)
        rw [(mSl a).mp ma, Bool.or_true] at this
        exact Option.isSome_iff_ne_none.mp this
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom, .atom "nil", []), ([], .map R, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          intro κ
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
          cases κ with
          | atom s =>
            rw [keyA]
            have i := inclA s
            simp only [hx, hy, amemV, Bool.not_eq_true'] at i
            simp only [SplitKey, memA, mSl, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
            constructor
            · rintro ((h | ⟨N, e, -⟩) | ⟨N, e, h⟩)
              · exact i h
              · cases e
              · cases e
                have := mR (.atom s)
                rw [h] at this
                cases hd : (mapLookup Dn (.atom s)).isSome
                · rfl
                · simp [hd] at this
            · intro h
              by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
              · exact Or.inl (Or.inl hs)
              · refine Or.inr ⟨R, rfl, ?_⟩
                have := mR (.atom s)
                simp only [h, Bool.false_or] at this
                simp only [Bool.not_eq_true] at hs
                rw [hs] at this
                cases hR : mapLookup R (.atom s)
                · rfl
                · rw [hR] at this; cases this
          | dom k i =>
            simp only [SplitKey, List.not_mem_nil, false_or]
            exact dsK k i
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .map R, Term.list rds, Term.list odds], ?_, Or.inr (Or.inr ⟨Sl, R, rds, odds, rfl, ?_, ?_, hA, fun κ => ?_⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom, .atom "nil", []), ([], .map R, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          intro sp msp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at msp
          rcases msp with rfl | rfl
          · exact ⟨⟨atomsOf Sl, Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
          · exact (okNeg R ha _ List.mem_cons_self)
        simpa using (hok _ (List.mem_cons_of_mem _ List.mem_cons_self)).1
      · have hna : ∀ N', Term.map R = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aR
        exact hna _ rfl
      · rw [← hk κ]
        cases κ <;> simp [SplitKey]
    · -- Static and dynamic atoms: the static ones, and the dynamic ones they miss.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_sub aDD aSS
      obtain ⟨Rl, rRl, mRl⟩ := aset_list aR (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inr ⟨Dn, hy⟩))
      have hrs : ∀ r ∈ Sl.map Term.atom ++ Rl.map Term.atom, ∃ s, r = .atom s := fun r mr =>
        (List.mem_append.mp mr).elim (atomsOf Sl r) (atomsOf Rl r)
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom ++ Rl.map Term.atom, .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          have i := inclA s
          simp only [hx, hy, amemV] at i
          simp only [SplitKey, List.mem_append, memA, mSl, mRl, mR, hy, amemV]
          constructor
          · rintro ((h | h) | ⟨N, e, -⟩)
            · exact i h
            · exact (Bool.and_eq_true_iff.mp h).1
            · cases e
          · intro h
            by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
            · exact Or.inl (Or.inl hs)
            · exact Or.inl (Or.inr (by simp [h, hs]))

      refine ⟨.tuple #[Term.list (Sl.map Term.atom), Term.list (Rl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨Sl.map Term.atom, Rl.map Term.atom, rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom ++ Rl.map Term.atom, .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ hrs na
        simpa using (hok _ List.mem_cons_self).1

end


/-! The maps of updates at keys of the shapes, as those of static splits. -/

section
variable {t : Term} {n : Nat}

/-- Static keys split in one of the shapes. -/
theorem static_gform {k : Term} (hk : DE (level t n).E k)
    (hU : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s)
    (hNeg : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S]) →
      ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧ GForm s (KeyPt t n k) := by
  obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ := key_split_any hk hU hNeg hm
  refine ⟨_, rk, ?_⟩
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · exact Or.inl ⟨rs, [], ds, [], by simp [splitT, Term.list], by simpa using ok, fun κ => by simpa using sk κ⟩
  · obtain rfl := nr N rfl
    exact Or.inr (Or.inl ⟨N, ds, [], by simp [splitT, Term.list], by simpa using ok, na N rfl,
      fun κ => by simpa using sk κ⟩)

end

/-- Static splits: of atoms, of the atoms outside a negated set, or of required atoms inside one, with keys `KP`. -/
def SForm (s : Term) (KP : MKey → Prop) : Prop :=
  (∃ rs Ds : List Term, s = splitT rs (.atom "nil") Ds ∧ SplitOk rs (.atom "nil") Ds ∧
    ∀ κ, SplitKey rs (.atom "nil") Ds κ ↔ KP κ) ∨
  (∃ (N : List (Term × Term)) (Ds : List Term), s = splitT [] (.map N) Ds ∧ SplitOk [] (.map N) Ds ∧
    (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∀ κ, SplitKey [] (.map N) Ds κ ↔ KP κ) ∨
  (∃ (A : List String) (N : List (Term × Term)) (Ds : List Term), s = splitT (A.map Term.atom) (.map N) Ds ∧
    SplitOk [] (.map N) Ds ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ (∀ a ∈ A, mapLookup N (.atom a) ≠ none) ∧
    ∀ κ, ((∃ a ∈ A, κ = .atom a) ∨ SplitKey [] (.map N) Ds κ) ↔ KP κ)

theorem splitOk_swap {rs : List Term} {neg : Term} {A B : List Term} (h : SplitOk rs neg (A ++ B)) :
    SplitOk rs neg (B ++ A) :=
  ⟨h.hrs, h.hneg, fun d md => h.hds d (List.mem_append.mpr (List.mem_append.mp md).symm),
    ⟨fun m => h.hatom.mp (List.mem_append.mpr (List.mem_append.mp m).symm),
     fun e => List.mem_append.mpr (List.mem_append.mp (h.hatom.mpr e)).symm⟩⟩

theorem splitKey_swap {rs : List Term} {neg : Term} {A B : List Term} (κ : MKey) :
    SplitKey rs neg (B ++ A) κ ↔ SplitKey rs neg (A ++ B) κ := by
  cases κ <;> simp [SplitKey, or_comm]

/-- Splits of the shapes update with the maps of static splits. -/
theorem dnf_gform_relB {s : Term} {KP : MKey → Prop} (hs : GForm s KP) (md : String) (hmd : Mode md) :
    ∃ s', SForm s' KP ∧ ∀ (m : Nat) (bdd dnf c st₁ st₂ : Term) {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s (.tuple #[c, .atom md])
        (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' (.tuple #[c, .atom md])
        (.atom "true") st₂ = .ok r₂ → RelB r₁ r₂ := by
  have sel : ∀ (Ds Ds' : List Term), ∃ L : List Term, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) ∧
      (md = "reject" → L = Ds' ++ Ds) ∧ (md ≠ "reject" → L = Ds ++ Ds') := fun Ds Ds' => by
    by_cases h : md = "reject"
    · exact ⟨Ds' ++ Ds, Or.inr rfl, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨Ds ++ Ds', Or.inl rfl, fun h' => absurd h' h, fun _ => rfl⟩
  have okL : ∀ {rs neg} {Ds Ds' L : List Term}, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) → SplitOk rs neg (Ds ++ Ds') →
      SplitOk rs neg L := fun hL ok => by rcases hL with rfl | rfl; exact ok; exact splitOk_swap ok
  have keyL : ∀ {rs neg} {Ds Ds' L : List Term}, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) → ∀ κ,
      SplitKey rs neg L κ ↔ SplitKey rs neg (Ds ++ Ds') κ := fun hL κ => by
    rcases hL with rfl | rfl; exact Iff.rfl; exact splitKey_swap κ
  rcases hs with ⟨Rs, Os, Ds, Ds', rfl, ok, sk⟩ | ⟨N, Ds, Ds', rfl, ok, na, sk⟩ | ⟨A, N, Ds, Ds', rfl, ok, na, hA, sk⟩
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT (Rs ++ Os) (.atom "nil") L, Or.inl ⟨_, L, rfl, okL hL ok, fun κ => (keyL hL κ).trans (sk κ)⟩, ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    refine dnf_opt_relB m bdd dnf Rs Os Ds Ds' c md hmd st₁ st₂ h₁ ?_
    by_cases h : md = "reject"
    · rw [ite_eq_left h, ← hr h]; exact h₂
    · rw [ite_eq_right h, ← hn h]; exact h₂
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT [] (.map N) L, Or.inr (Or.inl ⟨N, L, rfl, okL hL ok, na, fun κ => (keyL hL κ).trans (sk κ)⟩), ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    rcases hmd with rfl | rfl | rfl
    · exact dnf_neg_relB_force m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_keep m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_reject m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hr rfl] at *; exact h₂)
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT (A.map Term.atom) (.map N) L, Or.inr (Or.inr ⟨A, N, L, rfl, okL hL ok, na, hA,
      fun κ => (or_congr_right (keyL hL κ)).trans (sk κ)⟩), ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    rcases hmd with rfl | rfl | rfl
    · exact dnf_neg_relB_force m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_keep m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_reject m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hr rfl] at *; exact h₂)

theorem static_split_rel_ne (m : Nat) (descr s s' op st₁ st₂ : Term) (hd : descr ≠ .atom "term")
    (HR : ∀ bdd dnf {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s op (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' op (.atom "true") st₂ = .ok r₂ →
      RelB r₁ r₂) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s op (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s' op (.atom "true") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (HR _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)
    | trace_state

/-- `map_update_static/5` on splits updating with the same maps gives the same maps. -/
theorem static_split_rel (m : Nat) (descr s s' op st₁ st₂ : Term)
    (HR : ∀ bdd dnf {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s op (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' op (.atom "true") st₂ = .ok r₂ →
      RelB r₁ r₂) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s op (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s' op (.atom "true") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_split_rel_ne m _ s s' op st₁ st₂ (by simp) HR h₁ h₂
  · exact static_split_rel_ne m descr s s' op st₁ st₂ h HR h₁ h₂

section
variable {t : Term} {n : Nat}

/-- The maps an update with a key of keys `KP` may give: those of some static split of keys in `KP`. -/
def KRSem (t : Term) (n : Nat) (X : List (Term × Term)) (KP : MKey → Prop) (v : Term) (keep : Bool)
    (w : MW (level t n).V) : Prop :=
  ∃ (rs Ds Dm : List String) (neg : Term), SplitOk (rs.map Term.atom) neg (Ds.map Term.atom) ∧
    (∀ N, neg = .map N → rs = []) ∧ (∀ κ, SplitKey (rs.map Term.atom) neg (Ds.map Term.atom) κ → KP κ) ∧
    (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) ∧
    UpdSemKR (level t n).den (MT t n X) rs neg Dm v keep w

theorem strs_of {l : List Term} (h : ∀ r ∈ l, ∃ s, r = .atom s) : ∃ A : List String, l = A.map Term.atom :=
  atoms_of h

theorem ds_of {l : List Term} (h : ∀ d ∈ l, ∃ s ∈ domainKinds, d = .atom s) :
    ∃ A : List String, l = A.map Term.atom ∧ ∀ s ∈ A, s ∈ domainKinds := by
  obtain ⟨A, rfl⟩ := atoms_of fun d md => let ⟨s, _, e⟩ := h d md; ⟨s, e⟩
  refine ⟨A, rfl, fun s ms => ?_⟩
  obtain ⟨s', ms', e⟩ := h _ (List.mem_map_of_mem ms)
  cases e; exact ms'

/-- `:keep` and `:reject` of a static value at a key of the shapes, on a static map type, for either flag. -/
theorem kr_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {s : Term} {KP : MKey → Prop}
    (hs : GForm s KP) {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z)
    (vne : ∃ x, (level t n).den v x) (keep : Bool) (st : Term) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (keepOp v keep) (.atom "true") st =
      .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → KRSem t n X KP v keep w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have hmd : Mode (if keep then "keep" else "reject") := by cases keep <;> simp [Mode]
  have eop : keepOp v keep = .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]],
      .atom (if keep then "keep" else "reject")] := rfl
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  -- No map field: no maps.
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  -- The static split.
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X) s' (keepOp v keep)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s s' (keepOp v keep) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S S' : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S → (∀ w, S w → S' w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → S' w := by
    rintro r Yr S S' hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact hS w ((sr w).mp h')
  rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
  · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
    obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep ok (fun N e => nomatch e)
        (fun N e => nomatch e) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨rs', Ds', Dm, .atom "nil", ok, (fun N e => nomatch e),
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep (rk := []) ok (fun _ _ => rfl)
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl,
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    have hat : "atom" ∈ Ds' := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep rfl hDs hat hA
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      refine toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ?_)
      rcases h with h | ⟨a, ma, h⟩
      · exact ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl, fun κ h' => (sk κ).mp (Or.inr h'), mDm, h⟩
      · refine ⟨A, [], [], .atom "nil", ⟨fun r mr => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩,
          Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, (fun N e => nomatch e), fun κ h' => ?_,
          fun d => by simp, Or.inl ⟨rfl, Or.inl ⟨a, ma, h⟩⟩⟩
        cases κ with
        | atom s' => rcases h' with h' | ⟨N, e, -⟩
                     · obtain ⟨a', ma', e⟩ := List.mem_map.mp h'; exact (sk _).mp (Or.inl ⟨a', ma', by injection e with e; rw [e]⟩)
                     · cases e
        | dom k' i => simp [SplitKey] at h'


/-- The maps a delete with a key of keys `KP` may give: those of some static split of keys in `KP`. -/
def DelGSem (t : Term) (n : Nat) (X : List (Term × Term)) (KP : MKey → Prop) (md : String)
    (w : MW (level t n).V) : Prop :=
  ∃ (rs Ds Dm : List String) (neg : Term), SplitOk (rs.map Term.atom) neg (Ds.map Term.atom) ∧
    (∀ N, neg = .map N → rs = []) ∧ (∀ κ, SplitKey (rs.map Term.atom) neg (Ds.map Term.atom) κ → KP κ) ∧
    (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) ∧
    UpdSemD (level t n).den (MT t n X) rs neg Dm md w

/-- Deleting a key of the shapes, on a static map type, for either flag. -/
theorem del_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {s : Term} {KP : MKey → Prop}
    (hs : GForm s KP) {md : String} (hmd : Mode md) (st : Term) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (cOp (.map []) Bool.true md) (.atom "true") st =
      .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → DelGSem t n X KP md w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have eop : cOp (.map []) Bool.true md = .tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]],
      .atom md] := rfl
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  -- No map field: no maps.
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  -- The static split.
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X) s' (cOp (.map []) Bool.true md)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s s' (cOp (.map []) Bool.true md) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S S' : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S → (∀ w, S w → S' w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → S' w := by
    rintro r Yr S S' hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact hS w ((sr w).mp h')
  rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
  · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
    obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static (st := Bool.true) ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd ok (fun N e => nomatch e)
        (fun N e => nomatch e) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨rs', Ds', Dm, .atom "nil", ok, (fun N e => nomatch e),
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static (st := Bool.true) ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd (rk := []) ok (fun _ _ => rfl)
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl,
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    have hat : "atom" ∈ Ds' := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd rfl hDs hat hA
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      refine toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ?_)
      rcases h with h | ⟨a, ma, h⟩
      · exact ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl, fun κ h' => (sk κ).mp (Or.inr h'), mDm, h⟩
      · refine ⟨A, [], [], .atom "nil", ⟨fun r mr => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩,
          Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, (fun N e => nomatch e), fun κ h' => ?_,
          fun d => by simp, Or.inl ⟨rfl, Or.inl ⟨a, ma, h⟩⟩⟩
        cases κ with
        | atom s' => rcases h' with h' | ⟨N, e, -⟩
                     · obtain ⟨a', ma', e⟩ := List.mem_map.mp h'; exact (sk _).mp (Or.inl ⟨a', ma', by injection e with e; rw [e]⟩)
                     · cases e
        | dom k' i => simp [SplitKey] at h'

end


section
variable {t : Term} {n : Nat}

/-- `map_split_keys_and_domains/1` on a gradual key type of the laws: a split of the shapes, with the keys of the upper
bound. -/
theorem key_gform {k : Term} {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : «arrows_gradual?/2» (D (m + 1)) k (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      GForm s (KeyPt t n (upper k)) := by
  have static : «arrows_static?/2» k (.tuple #[.integer n, t]) = .ok (.atom "true") → ∃ s,
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      GForm s (KeyPt t n (upper k)) := by
    intro hs
    have dk := arrows_static_ok hs
    rw [upper_tc dk]
    exact static_gform dk (fun Y e => by subst e; exact static_union_atoms hs)
      (fun Y e => by subst e; exact static_negation_atoms hs) hm
  have gk := arrows_gradual_gc (t := t) (n := n) (m := m + 1) (by omega) k (by simpa [Term.true] using h)
  unfold «arrows_gradual?/2» at h
  cases k with
  | map X =>
    cases hD : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, hD] at h; exact static h
    | some Dy =>
      simp only [getMapKeys_single, hD, Option.toList, Erlang.maps.«remove/2», Lynx.Except.ok_bind,
        Lynx.Except.andAlso_eq_true, equalExact_eq_decide] at h
      obtain ⟨⟨hS, hDy⟩, -⟩ := h
      rw [← rmDyn] at hS
      have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
      rw [upper_dyn hD]
      exact gsplit_form gk hD (fun tag S e ht => static_atom_set hS tag S (lX.trans e) ht)
        (fun Y e tag S e' ht => by subst e; exact static_atom_set hDy tag S e' ht) hm
  | _ => simp at h; exact static h

/-- Forcing a static value at a split putting with `P`, on a static map type, for either flag, asking for the old
values: the maps the puts give. -/
theorem force_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {Rk Ok neg' Rd Od neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts (.tuple #[Rk, Ok, neg', Rd, Od]) neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (st : Term) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (.tuple #[Rk, Ok, neg', Rd, Od])
      (forceOp v) (.atom "true") st = .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → P (level t n).den (MT t n X) v w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨Y', f', rfl, -, -, hY⟩⟩ :=
    dput_update_static_g hP hNa ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv hb fb
  · rcases static_rt_rel (k + 6) (.map X) _ _ _ _ _ _ _ _ run (by rw [show k + 2 + 6 = k + 6 + 2 by omega] at rr; exact rr)
      with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
  rcases static_rt_rel (k + 6) (.map X) _ _ _ _ _ _ _ _ run (by rw [show k + 2 + 6 = k + 6 + 2 by omega] at rr; exact rr)
    with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
  · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
    obtain ⟨-, rfl, -⟩ := e
    rw [conv] at hY
    rcases hY with ⟨rfl, -⟩ | ⟨r, rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact (sr w).mp h'
  · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂
    obtain ⟨-, rfl, -⟩ := e₁
    obtain ⟨-, rfl, -⟩ := e₂
    rw [conv] at hY
    rcases hY with ⟨rfl, -⟩ | ⟨r, rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact (sr w).mp h'

end


/-! Upper bounds of updates of gradual map types. -/


section
variable {t : Term} {n : Nat}

theorem single_map_only {Y : List (Term × Term)} (hY : Y = [] ∨ ∃ r, Y = [(.atom "map", r)]) (q : PN t n)
    (hq : denD (.map Y) q) : q.1.1 = "map" := by
  rcases hY with rfl | ⟨r, rfl⟩
  · simp [denD_map, mapLookup, dn_none] at hq
  · rw [denD_map] at hq
    by_cases e : q.1.1 = "map"
    · exact e
    · simp [mapLookup, e, dn_none] at hq

/-- Updates of gradual map types at the upper bound: the maps the update gives from the static part or from the
dynamic part. -/
theorem upd_upper_gen {M : List (Term × Term)} (gM : GC (level t n) (.map M)) {s op : Term} {m : Nat}
    (hm : (level t n).K + 14 ≤ m + 1) {Sm : (MW (level t n).V → Prop) → MW (level t n).V → Prop}
    (hsem : ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ st T Y er f,
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map X) s op (.atom "true") st =
        .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
        ∀ w, MT t n Y' w → Sm (MT t n X) w)
    (hDy : ∀ Dy, mapLookup M (.atom "dynamic") = some Dy → ∃ DX, Dy = .map DX) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map M) s op (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    GC (level t n) R ∧ (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
      ∀ w, denD (upper R) (mpt (t := t) (n := n) w) → Sm (MT t n (rmDyn M)) w ∨
        ∃ DX, mapLookup M (.atom "dynamic") = some (.map DX) ∧ Sm (MT t n DX) w := by
  cases hD : mapLookup M (.atom "dynamic") with
  | none =>
    have dM := GC.static gM hD
    obtain ⟨f, hs⟩ := static_upd_inv hD run
    obtain ⟨Y', rfl, dY, shY, sY⟩ := hsem M dM _ _ _ _ _ hs
    refine ⟨GC.tc dY, fun q hq => single_map_only shY q (by rwa [upper_tc dY] at hq), fun w h => Or.inl ?_⟩
    rw [upper_tc dY, denD_mpt] at h
    rw [rmDyn_static hD]
    exact sY w h
  | some Dy =>
    obtain ⟨DX, rfl⟩ := hDy _ hD
    obtain ⟨dDy, -⟩ : DE (level t n).E (.map DX) ∧ True := by
      rcases gM with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, -, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, trivial⟩
    obtain ⟨Yd, res, sd, ⟨Td, ed, fd, hdy⟩, sYd, hres, hsd, hR⟩ := grad_upd_inv hD (fun Td Yd ed fd h => by
      obtain ⟨Y', rfl, -, shY, -⟩ := hsem DX dDy _ _ _ _ _ h
      refine ⟨Y', rfl, ?_⟩
      rcases shY with rfl | ⟨r, rfl⟩ <;> simp [mapLookup]) run
    obtain ⟨Yd', eYd, dYd, shYd, sYd'⟩ := hsem DX dDy _ _ _ _ _ hdy
    cases eYd
    -- The static part.
    obtain ⟨SD, rfl, dSD, shSD, sSD⟩ : ∃ SD, sd = .map SD ∧ DE (level t n).E (.map SD) ∧
        (SD = [] ∨ ∃ r, SD = [(.atom "map", r)]) ∧ ∀ w, MT t n SD w → Sm (MT t n (rmDyn M)) w := by
      rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩
      · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
      · exact hsem (rmDyn M) gM.low_tc _ _ _ _ _ hres
    have gA : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) := by
      refine Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, ?_, fun v hv => ?_⟩
      · rw [show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]]; exact descrC_nil
      · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
        simp [denD_map, mapLookup, dn_none] at hv
    obtain ⟨c, gc, rc, -, uc⟩ := gc_opt_union (GC.tc dSD) gA [] (m := m + 1) hm
    rw [show Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) (.map SD) (.map [(.atom "dynamic", .map Yd)]) =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (.map SD) (.map [(.atom "dynamic", .map Yd)]) (.map []) from rfl,
      rc] at hR
    cases hR
    have upA : upper (.map [(.atom "dynamic", .map Yd)]) = .map Yd := by simp [upper, mapLookup]
    refine ⟨gc, fun q hq => ?_, fun w h => ?_⟩
    · rcases (uc q).mp hq with h | h
      · rw [upper_tc dSD] at h; exact single_map_only shSD q h
      · rw [upA] at h; exact single_map_only shYd q h
    · rcases (uc _).mp h with h | h
      · rw [upper_tc dSD, denD_mpt] at h; exact Or.inl (sSD w h)
      · rw [upA, denD_mpt] at h; exact Or.inr ⟨DX, rfl, sYd' w h⟩

end

/-- `map_update/5` with a gradual value updates the dynamic part of the map type with the value's dynamic part. -/
theorem upd5_gval {m : Nat} (X : List (Term × Term)) {key mode s : Term} {Zv : List (Term × Term)} {Dv : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv)
    (hmo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "true")) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.map Zv) mode (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (dynG X)) s
        (.tuple #[.tuple #[.atom "constant", .tuple #[Dv, .atom "false"]], mode]) (.atom "true") := by
  have hmo' : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (X.filter fun entry =>
      !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq))) =
      .ok (.atom "true") := hmo
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rw [Elixir.Module.Types.Descr.«map_gradual/1».eq_def]
  cases hX : mapLookup X (.atom "dynamic") <;>
    rcases hmode with rfl | rfl | rfl <;>
    simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk, getMapKeys_single, hZ, hX,
      dynG, Erlang.maps.«remove/2», hmo'] <;> rfl

/-- `map_update/5` with a gradual value on a map type whose static part may hold something other than maps:
`:badmap`. -/
theorem upd5_gval_bad {m : Nat} (X : List (Term × Term)) {key mode s : Term} {Zv : List (Term × Term)} {Dv : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv)
    (hmo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "false")) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.map Zv) mode (.atom "true") = .ok (.atom "badmap") := by
  have hmo' : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (X.filter fun entry =>
      !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq))) =
      .ok (.atom "false") := hmo
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rw [Elixir.Module.Types.Descr.«map_gradual/1».eq_def]
  rcases hmode with rfl | rfl | rfl <;>
    simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk, getMapKeys_single, hZ,
      Erlang.maps.«remove/2», hmo', Elixir.Module.Types.Descr.«map_update_unchecked/4»]


/-- `empty?/1` of a gradual type is that of its dynamic part. -/
theorem empty_gval {Zv : List (Term × Term)} {Dv : Term} (hZ : mapLookup Zv (.atom "dynamic") = some Dv)
    (sD : Dv = .atom "term" ∨ ∃ DX, Dv = .map DX ∧ mapLookup DX (.atom "dynamic") = none) (m : Nat) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) (.map Zv) = Elixir.Module.Types.Descr.«empty?/1» (D m) Dv := by
  rcases sD with rfl | ⟨DX, rfl, sX⟩
  · simp only [Elixir.Module.Types.Descr.«empty?/1»]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, hZ]
  · simp only [Elixir.Module.Types.Descr.«empty?/1»]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def, Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, hZ, sX]

end Elixir.STTDescrProofsTest.Nest
