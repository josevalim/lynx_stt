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
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
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
          · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
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
