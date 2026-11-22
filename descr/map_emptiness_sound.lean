namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

theorem domKind_mem (k : Fin 11) : domKind k ∈ domainKinds := by
  revert k; decide

/-- `map_line_empty?/4` answers `true` only when its negations cover every map of the line. -/
theorem line_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 3 ≤ m) {S : List (Term × Term)} (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, MapLitV E t) → ∀ tag : Term, TagV E tag →
      ∀ l, FieldsV E l → Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
        (Term.list negs) (.map S) = .ok (.atom "true") → ∀ w, MSem den tag l w → CovM den negs w := by
  intro negs
  induction negs with
  | nil =>
    intro _ tag _ l _ run
    rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def] at run
    simp at run
  | cons N rest ih =>
    intro lits tag gt l sl run w hw
    obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, MapLitV E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    have later : CovM den rest w → CovM den (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest) w :=
      fun ⟨N, mN, hN⟩ => ⟨N, List.mem_cons_of_mem _ mN, hN⟩
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact ⟨_, List.mem_cons_self, nsem_lit.mpr ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩⟩
    by_cases skip : tag = .atom "open" ∧ ntag = .atom "closed"
    · obtain ⟨rfl, rfl⟩ := skip
      rw [list_cons, Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def] at run
      exact later (ih lits' _ gt l sl (by simpa using run) w hw)
    by_cases cov : CovM den rest w
    · exact later cov
    have lineS := fun l' (sl' : FieldsV E l') r w' (hw' : MSem den tag l' w') => ih lits' tag gt l' sl' r w' hw'
    have hl : ∀ e ∈ l, FieldValue E e.2 := fun e me => (sl.1 e me).2
    have hnl : ∀ e ∈ nl, FieldValue E e.2 := fun e me => (snl.1 e me).2
    have ih' := map_line_total ops dops jops S rest fun t mt => (lits' t mt).plain
    have ops' := ops.mono (Nat.le_add_right K 3)
    have dops' := dops.mono (Nat.le_add_right K 3)
    have lineT : ∀ l', FieldsV E l' → ∃ b : Bool, Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
        (fieldsTerm l') (Term.list rest) (.map S) = .ok (boolAtom b) := fun l' sl' => by
      obtain ⟨b, hb⟩ := ih' tag gt.plain l' fun e me => (sl'.1 e me).2
      exact ⟨b, hb m hm⟩
    obtain ⟨bc, runc, incl⟩ := check_val ops dops esem (m := m) (by omega) hS gt gn skip
    obtain ⟨c, hor, hc⟩ := walk_choice (tag := tag) (ntag := ntag)
    obtain ⟨bk, hk⟩ := ih' tag gt.plain l hl
    have hk' := hk m hm
    dsimp only at hk'
    -- the remaining negations answer `false`, as they do not cover the map
    have nk : bk = Bool.false := by
      cases bk
      · rfl
      · exact absurd (lineS l sl (by simpa [boolAtom] using hk') w hw) cov
    subst nk
    -- so the negated literal holds the map
    refine ⟨_, List.mem_cons_self, ?_⟩
    have falseRun : ∀ (hf : bc = Bool.false → Bool.false = Bool.false) ht hw',
        Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
          (Term.list (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest)) (.map S) = .ok (boolAtom Bool.false) :=
      fun hf ht hw' => line_general top skip runc hor hk' hf ht hw'
    cases bc
    · rw [falseRun (fun _ => rfl) (fun h => nomatch h) (fun h => nomatch h)] at run
      simp [boolAtom] at run
    cases c
    · rcases fields_total ops' dops' S gt.plain gn.plain (Term.list rest) l hl (fun l' hl' => ih' tag gt.plain l' hl') _ l
          nl (Nat.le_refl _) hl hnl with ⟨b, hb⟩ | hb
      · have r := line_general (k := k) (b := b) top skip runc hor hk' (fun h => nomatch h) (fun _ h => nomatch h)
          (fun _ _ => Or.inl (hb m hm))
        rw [r] at run
        cases b
        · simp [boolAtom] at run
        have walk : Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
            (fieldsTerm l) (Term.list rest) (.map S) = .ok (.atom "true") := by simpa [boolAtom] using hb m hm
        have keys := fields_sound ops dops esem (by omega) hS gt gn sl lineS snl hw cov _ [] l [] nl (Nat.le_refl _)
          (by simp) (by simp) (by simp) walk
        have tin := incl.mp rfl
        refine nsem_lit.mpr ⟨fun s => ?_, fun k i => tin _ (domKind_mem k) _ (hw.doms k i)⟩
        by_cases hs : ∃ e ∈ l ++ nl, e.1 = Term.atom s
        · obtain ⟨e, me, es⟩ := hs
          exact keys e me s es
        · have n₁ : mapLookup l (.atom s) = Option.none := lookup_none fun e me eq => hs ⟨e, by simp [me], eq⟩
          have n₂ : mapLookup nl (.atom s) = Option.none := lookup_none fun e me eq => hs ⟨e, by simp [me], eq⟩
          have := hw s
          simp only [FSem, n₁] at this
          simp only [FSem, n₂]
          exact tin "atom" (by simp [domainKinds]) _ this
      · rw [falseRun (fun _ => rfl) (fun _ h => nomatch h) (fun _ _ => Or.inr ⟨hb m hm, rfl⟩)] at run
        simp [boolAtom] at run
    · have tagOk := hc.mp rfl
      rcases disjoint_total ops jops S gt.plain gn.plain _ l nl (Nat.le_refl _) hl hnl [] (by simp) with dis | ⟨es, hes, r6⟩
      · rw [falseRun (fun _ => rfl) (fun _ _ => ⟨_, by simpa [entriesTerm] using dis m hm, Or.inl ⟨rfl, rfl⟩⟩)
          (fun _ h => nomatch h)] at run
        simp [boolAtom] at run
      obtain ⟨b5, h5⟩ := meet5_total ops' dops' S tag (Term.list rest) (fun l' hl' => ih' tag gt.plain l' hl') es hes []
        (by simp)
      have r := line_general (k := k) (b := b5) top skip runc hor hk' (fun h => nomatch h)
        (fun _ _ => ⟨_, by simpa [entriesTerm] using r6 m hm, Or.inr ⟨es, rfl, by simpa [fieldsTerm] using h5 m hm⟩⟩)
        (fun _ h => nomatch h)
      rw [r] at run
      cases b5
      · simp [boolAtom] at run
      have meetRun := h5 m hm
      rcases align_sound ops dops esem jops hm hS tag ntag gt gn tagOk rest lineT lineS nl snl _ l nl (Nat.le_refl _) sl
          [] [] (by simp) (by simp) with dis | ⟨es', r6', ok⟩
      · have := (r6 m hm).symm.trans dis
        simp [entriesTerm] at this
        cases es <;> simp [Term.list] at this
      · have same : entriesTerm es = entriesTerm es' := by
          have := (r6 m hm).symm.trans r6'
          simpa using this
        rcases ok [] (by simpa using sl) (by simp) (by simp) (by simp)
            (by rw [← same]; simpa [fieldsTerm, boolAtom] using meetRun) w (by simpa using hw) with h | h
        · exact nsem_lit.mpr h
        · exact absurd h cov

/-- `init_map_line_empty?/4` answers `true` only when its negations cover every map of the line. -/
theorem init_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 4 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {tag : Term} (gt : TagV E tag) {l : List (Term × Term)}
    (sl : FieldsV E l) {negs : List Term} (lits : ∀ t ∈ negs, MapLitV E t)
    (run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D m) tag (fieldsTerm l) (Term.list negs)
      (.map S) = .ok (.atom "true")) :
    ∀ w, MSem den tag l w → CovM den negs w := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  have each : ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]),
      Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2» (D n) (.map S) x = .ok (boolAtom (reqEmpty den x)) := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := (sl.1 e me).2
    rw [ho]
    cases o
    · obtain ⟨b, hb⟩ := ops.empty ht S
      have run := hb n (by omega)
      have sem := esem.empty ht hS (by omega) run
      simp only [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, Bool.false_eq_true,
        ite_false, reqEmpty]
      rw [run]
      cases b <;> simp at sem <;> simp [sem, boolAtom]
    · simp [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom, reqEmpty]
  have anyRun := any_list (D (n + 1)) _ _ _ (reqEmpty den) _ fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-init_map_line_empty?/4-fun-0-/1».pure]
    exact each x mx
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def] at run
  simp only [fieldsTerm] at anyRun run
  simp only [pure_bind, anyRun] at run
  intro w hw
  cases hany : (l.map fun e => Term.tuple #[e.1, e.2]).any (reqEmpty den)
  · rw [hany] at run
    have := line_sound ops dops esem jops (show K + 3 ≤ n + 1 by omega) hS negs lits tag gt l sl
      (by simpa [boolAtom, Lynx.Except.orElse, fieldsTerm] using run) w hw
    exact this
  · exfalso
    obtain ⟨x, mx, rx⟩ := List.any_eq_true.mp hany
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := (sl.1 e me).2
    obtain ⟨s, es⟩ := (sl.1 e me).1
    have look := lookup_of_mem sl me es
    have := hw s
    unfold FSem at this
    rw [look, ho] at this
    simp only at this
    rw [fieldSem_mk] at this
    rw [ho] at rx
    cases o
    · simp [reqEmpty, boolAtom] at rx
      rcases this with ⟨-, h⟩ | ⟨y, -, hy⟩
      · cases h
      · exact rx y hy
    · simp [reqEmpty] at rx

/-- `map_bdd_empty?/4` answers `true` only when no map along the path, outside the negations, satisfies the BDD. -/
theorem map_bdd_sound (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    {m : Nat} (hm : K + 4 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") →
      ValUnsatM E den pos negs r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos →
    (∀ t ∈ negs, MapLitV E t) →
    Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") →
    ValUnsatM E den pos negs r) ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits run w hw nn
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    simp only at run
    obtain ⟨N, mN, hN⟩ := init_sound ops dops esem jops (by omega) hS gt sl lits run w (inPosM_iff.mp hw)
    exact (nn N mN hN).elim
  · intro ok _ pos negs _ _ _ w _ _
    rfl
  · intro ok k x y okl okLit pos negs hp lits run w hw nn
    have hl := okLit _ okl
    rw [eval_leaf]
    cases e : valM E den w (.tuple #[.integer k, x, y])
    · rfl
    exfalso
    have hlit := valM_lit ops dops esem hl e
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    rcases inter_val ops dops esem (m := m) (by omega) hS hp hl with ⟨empty, disj⟩ | ⟨pos', r', hp', sem'⟩
    · exact disj w hw hlit
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp'
    simp [r'] at run
    obtain ⟨N, mN, hN⟩ := init_sound ops dops esem jops (by omega) hS gt sl lits run w
      (inPosM_iff.mp ((sem' w).mpr ⟨hw, hlit⟩))
    exact nn N mN hN
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits run w hw nn
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    have hp₀ := hp
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def] at run
    rcases inter_val ops dops esem (m := m) (by omega) hS hp₀ hl with ⟨empty, disj⟩ | ⟨pos2, r2, hp2, sem2⟩
    · simp only [empty, Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at run
      obtain ⟨⟨rd, -⟩, ru⟩ := run
      have nl : valM E den w lit = Bool.false := by
        cases e : valM E den w lit
        · rfl
        · exact (disj w hw (valM_lit ops dops esem hl e)).elim
      have ed := idd okLit' _ (lit :: negs) hp₀ (fun t mt => by
        rcases List.mem_cons.mp mt with rfl | mt
        · exact hl
        · exact lits t mt) (by rwa [list_cons]) w hw (fun N mN hN => by
          rcases List.mem_cons.mp mN with rfl | mN
          · rw [valM_true hl hN] at nl; cases nl
          · exact nn N mN hN)
      have eu := iu okLit' _ negs hp₀ lits ru w hw nn
      simp [eval_node, nl, ed, eu]
    · have hp2' := hp2
      obtain ⟨tag2, l2, rfl, -⟩ := hp2
      simp only [r2, Lynx.Except.andAlso_eq_true, Lynx.Except.ok_bind] at run
      obtain ⟨⟨rd, rc⟩, ru⟩ := run
      have eu := iu okLit' _ negs hp₀ lits ru w hw nn
      cases e : valM E den w lit
      · have ed := idd okLit' _ (lit :: negs) hp₀ (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact lits t mt) (by rwa [list_cons]) w hw (fun N mN hN => by
            rcases List.mem_cons.mp mN with rfl | mN
            · rw [valM_true hl hN] at e; cases e
            · exact nn N mN hN)
        simp [eval_node, e, ed, eu]
      · have ec := ic okLit' _ negs hp2' lits rc w ((sem2 w).mpr ⟨hw, valM_lit ops dops esem hl e⟩) nn
        simp [eval_node, e, ec, eu]

end Elixir.STTDescrProofsTest.Nest
