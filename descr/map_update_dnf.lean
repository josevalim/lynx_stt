namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `upd_domains`, also giving the domains found: the kinds some line's tag allows. -/
theorem upd_domains2 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (cb : Term) (hcb : ∃ c : Bool, (D (n + 3)).pure cb #[] = .ok (boolAtom c))
    (Ds : List String) {acc : Term} (ha : E acc) :
    ∃ (f : Bool) (val mis : List Term) (T : Term),
      Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 4)) (Term.list lines) (Term.list (Ds.map Term.atom))
        acc (.atom "true") cb = .ok (.tuple #[boolAtom f, Term.list val, Term.list mis, T]) ∧ E T ∧
      (∀ x, den T x ↔ den acc x ∨ ∃ s ∈ Ds, ∃ L ∈ lines, LineTag den L s x) ∧ (Ds = [] → f = Bool.false) ∧
      (∀ d ∈ mis, ∃ s ∈ Ds, d = .atom s) ∧
      (∀ d, d ∈ val ↔ ∃ s ∈ Ds, d = .atom s ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x) ∧ (val ≠ [] → f = Bool.true) := by
  obtain ⟨c, hc⟩ := hcb
  obtain ⟨r, ⟨f, val, mis, T, rfl, hT, sT, fD, mD, vD, vf⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_get_domains/5-fun-0-" #[Term.list lines, .atom "true", cb]
    (fun pre a => ∃ (f : Bool) (val mis : List Term) (T : Term), a = .tuple #[boolAtom f, Term.list val, Term.list mis, T] ∧
      E T ∧ (∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LineTag den L s x) ∧
      (pre = [] → f = Bool.false) ∧ (∀ d ∈ mis, d ∈ pre) ∧
      (∀ d, d ∈ val ↔ ∃ s, .atom s ∈ pre ∧ d = .atom s ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x) ∧
      (val ≠ [] → f = Bool.true))
    (Ds.map Term.atom) (fun pre x a mx ⟨f, val, mis, T, ea, hT, sT, fD, mD, vD, vf⟩ => by
      subst ea
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨g, rg, hg, sg⟩ := get_domain1 ef (n := n + 3) (by omega) lines hl s
      obtain ⟨b, rb, sb⟩ := ef.empty1 (m := n + 3) (by omega) hg
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hT hg (m := n + 3) (by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5», rg, rb, Lynx.Except.ok_bind,
        Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«==/2»]
      have semU : ∀ x, den u x ↔ den acc x ∨ ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ ∃ L ∈ lines, LineTag den L s' x :=
        fun x => by
          rw [su, sT, sg]
          simp only [List.mem_append, List.mem_singleton, Term.atom.injEq]
          constructor
          · rintro ((h | ⟨s', m', h⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨s', Or.inl m', h⟩
            · exact Or.inr ⟨s, Or.inr rfl, h⟩
          · rintro (h | ⟨s', m' | rfl, h⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨s', m', h⟩)
            · exact Or.inr h
      have semT : b = Bool.true → ∀ x, den T x ↔ den acc x ∨ ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ ∃ L ∈ lines, LineTag den L s' x :=
        fun eb x => by
          rw [sT]
          simp only [List.mem_append, List.mem_singleton, Term.atom.injEq]
          constructor
          · rintro (h | ⟨s', m', h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨s', Or.inl m', h⟩
          · rintro (h | ⟨s', m' | rfl, h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨s', m', h⟩
            · exact absurd ((sg x).mpr h) (sb.mp eb x)
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
      have vAdd : (∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ Term.atom s :: val ↔
          ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ d = .atom s' ∧ ∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro hs d
        rw [List.mem_cons, vD]
        constructor
        · rintro (rfl | ⟨s', m', e, h⟩)
          · exact ⟨s, by simp, rfl, hs⟩
          · exact ⟨s', List.mem_append_left _ m', e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases List.mem_append.mp m' with m' | m'
          · exact Or.inr ⟨s', m', rfl, h⟩
          · simp at m'; subst m'; exact Or.inl rfl
      have vKeep : (¬∃ L ∈ lines, ∃ x, LineTag den L s x) → ∀ d, d ∈ val ↔
          ∃ s', .atom s' ∈ pre ++ [.atom s] ∧ d = .atom s' ∧ ∃ L ∈ lines, ∃ x, LineTag den L s' x := by
        intro hs d
        rw [vD]
        constructor
        · rintro ⟨s', m', e, h⟩
          exact ⟨s', List.mem_append_left _ m', e, h⟩
        · rintro ⟨s', m', rfl, h⟩
          rcases List.mem_append.mp m' with m' | m'
          · exact ⟨s', m', rfl, h⟩
          · simp at m'; subst m'; exact absurd h hs
      by_cases sa : s = "atom"
      · subst sa
        cases b
        · refine ⟨_, ⟨Bool.true, .atom "atom" :: val, mis, u, rfl, hu, semU, by simp, fun d md => by simp [mD d md],
            vAdd (heldI.mp rfl), fun _ => rfl⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list]
        · have mis' : ∀ d ∈ Term.atom "atom" :: mis, d ∈ pre ++ [.atom "atom"] := fun d md => by
            rcases List.mem_cons.mp md with rfl | md
            · simp
            · simp [mD d md]
          cases c
          · refine ⟨_, ⟨f, val, .atom "atom" :: mis, T, rfl, hT, semT rfl, by simp, mis',
              vKeep (fun h => by have := heldI.mpr h; cases this), vf⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
          · refine ⟨_, ⟨Bool.true, val, .atom "atom" :: mis, T, rfl, hT, semT rfl, by simp, mis',
              vKeep (fun h => by have := heldI.mpr h; cases this), fun _ => rfl⟩, ?_⟩
            simp [boolAtom, Lynx.Term.isMember, Term.list, hc, Erlang.erlang.«/=/2», Lynx.Except.guard]
      · have ne : Term.compare (Term.fuel (.atom s) (.atom "atom")) (.atom s) (.atom "atom") ≠ .eq := by
          rw [atoms_cmp]; exact fun e => sa (Std.compare_eq_iff_eq.mp e)
        cases b
        · refine ⟨_, ⟨Bool.true, .atom s :: val, mis, u, rfl, hu, semU, by simp, fun d md => by simp [mD d md],
            vAdd (heldI.mp rfl), fun _ => rfl⟩, ?_⟩
          simp [boolAtom, Lynx.Term.isMember, Term.list, ne]
        · refine ⟨_, ⟨f, val, .atom s :: mis, T, rfl, hT, semT rfl, by simp, fun d md => ?_,
            vKeep (fun h => by have := heldI.mpr h; cases this), vf⟩, ?_⟩
          · rcases List.mem_cons.mp md with rfl | md
            · simp
            · simp [mD d md]
          · simp [boolAtom, Lynx.Term.isMember, Term.list, ne])
    (.tuple #[.atom "false", .nil, .nil, acc]) ⟨Bool.false, [], [], acc, rfl, ha, fun x => by simp, fun _ => rfl, by simp, by simp, fun h => absurd rfl h⟩
  refine ⟨f, val, mis, T, ?_, hT, fun x => by rw [sT]; simp, fun e => fD (by simp [e]), fun d md => ?_, fun d => ?_, vf⟩
  rotate_left 2
  · rw [vD]; simp
  · simpa [Elixir.Module.Types.Descr.«map_update_get_domains/5», boolAtom, Term.list] using run
  · obtain ⟨s, ms, rfl⟩ := List.mem_map.mp (mD d md); exact ⟨s, ms, rfl⟩


/-- The maps of an update at a key with `:keep` or `:reject`, from the maps of a type. -/
def KeepSemM (den : Term → V → Prop) (M : MW V → Prop) (v : Term) (keep : Bool) (a : String) (w : MW V) : Prop :=
  (PutAt den v a w ∧ ∃ x, M (setK a (some x) w)) ∨ (keep = Bool.true ∧ w (.atom a) = none ∧ M w)

/-- A type given by no map field or a single one, holding the maps of a set. -/
def MapsY (E : Term → Prop) (den : Term → V → Prop) (Y : Term) (S : MW V → Prop) : Prop :=
  (Y = .map [] ∧ ∀ w, ¬S w) ∨
    ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ S w

/-- The mode of `:keep` or `:reject`. -/
def modeS (keep : Bool) : String := if keep then "keep" else "reject"

theorem keepOp_cOp (v : Term) (keep : Bool) : keepOp v keep = cOp v Bool.false (modeS keep) := by
  cases keep <;> rfl

theorem mode_modeS (keep : Bool) : Mode (modeS keep) := by
  cases keep
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)

/-- Every kind of key is in a list. -/
def FullK (Ds : List String) : Prop := ∀ d ∈ domainKinds, d ∈ Ds

/-- The maps of `map_update_static_dnf/6` for `:keep` and `:reject` of a value, from the maps of a type: the updates
at the atoms of the split, or the box and the widened kinds, at the kinds `Dm` updated. -/
def UpdSemKR (den : Term → V → Prop) (M : MW V → Prop) (rs : List String) (neg : Term) (Dm : List String) (v : Term)
    (keep : Bool) (w : MW V) : Prop :=
  (neg = .atom "nil" ∧ ((∃ a ∈ rs, KeepSemM den M v keep a w) ∨ (Dm ≠ [] ∧ WRes den M v (modeS keep) Dm w))) ∨
  ∃ N, neg = .map N ∧
    ((keep = Bool.false ∧ FullK Dm ∧ BoxSem den M (setStrs N) v Bool.false (modeS keep) Dm w) ∨
     (¬(keep = Bool.false ∧ FullK Dm) ∧
       (BoxSem den M (setStrs N) v Bool.false (modeS keep) (Dm.filter (· = "atom")) w ∨
        (Dm.filter (· ≠ "atom") ≠ [] ∧ WRes den M v (modeS keep) (Dm.filter (· ≠ "atom")) w))))

theorem keepSem_iff {v : Term} {keep : Bool} {lines : List Term} {a : String} {w : MW V} :
    KeepSem den v keep lines a w ↔ KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w := by
  unfold KeepSem KeepSemM
  constructor
  · rintro (⟨p, L, mL, x, h⟩ | ⟨hk, hn, L, mL, h⟩)
    · exact Or.inl ⟨p, x, L, mL, h⟩
    · exact Or.inr ⟨hk, hn, L, mL, h⟩
  · rintro (⟨p, x, L, mL, h⟩ | ⟨hk, hn, L, mL, h⟩)
    · exact Or.inl ⟨p, L, mL, x, h⟩
    · exact Or.inr ⟨hk, hn, L, mL, h⟩

/-- The named keys of `map_update_static_dnf/6` for `:keep` and `:reject` of a value, asking for the old values: the
required atoms are built, and no optional ones. -/
theorem named_tail (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (A : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term} (hT₁ : E T₁)
    (errs : List Term) (bd : Term) (hbd : bd = .atom "true" ∨ bd = .atom "false") :
    ∃ (T' Er' : Term) (f' : Bool) (B' : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, Term.list errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T', Term.list B', Er', boolAtom f'])
        (Term.list lines) .nil (keepOp v keep) (.atom "false") (.atom "true") (.atom "true") bd =
        .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ (∀ b ∈ B', MField E b) ∧
      ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w := by
  classical
  let lk : String → Bool := fun a => decide (Lacking den lines a)
  have hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a := fun a => by simp [lk]
  obtain ⟨B', f', T', Er', e0, -, -, -, -, -, bT'⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.true Bool.true lk hlk A Bl fl T₁ (Term.list errs) hT₁
  obtain ⟨fB', sB'⟩ := bT' rfl fBl
  refine ⟨T', Er', f', B', by simpa using e0, ?_, fB', fun w => by rw [sB']; simp only [keepSem_iff]⟩
  rcases hbd with rfl | rfl <;> cases keep <;>
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, modeT]

/-- The union of the maps of `map_update_static_dnf/6`. -/
theorem union_Y (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (B : List Term) (fB : ∀ b ∈ B, MField E b)
    {S : MW V → Prop} (sB : ∀ w, (∃ b ∈ B, denMF E den b w = Bool.true) ↔ S w) :
    ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D m) (Term.list B) = .ok r ∧
      ((r = .atom "bdd_bot" ∧ ∀ w, ¬S w) ∨ (r ≠ .atom "bdd_bot" ∧ MField E r ∧ ∀ w, denMF E den r w = Bool.true ↔ S w)) := by
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := m) hm (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ B (Nat.le_refl _) fun b mb => ⟨fB b mb, by
      rcases fB b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  refine ⟨r, rr, ?_⟩
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    exact Or.inl ⟨rfl, fun w h => by have := (sr w).mpr ((sB w).mpr h); simp [denMF_bot] at this⟩
  · exact Or.inr ⟨bot, fr, fun w => (sr w).trans (sB w)⟩

/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a value at a finite set of atoms and some kinds, asking
for the old values. -/
theorem upd_dnf_nil (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) (A : List String)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hna : "atom" ∉ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Dm v keep) := by
  classical
  have m₂ : Erlang.erlang.«++/2» (Term.list (A.map Term.atom)) .nil = .ok (Term.list (A.map Term.atom)) := by
    simpa using append_list (A.map Term.atom) []
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => compareExact (x.fuel y) x y == .eq) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have mm : Erlang.erlang.«--/2» .nil (Term.list (A.map Term.atom)) = .ok .nil := by
    simp [Erlang.erlang.«--/2», Term.properList?, e00, Term.list]
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ [])
  have hcb : (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, .nil, Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», m₂, Lynx.Except.ok_bind]
    simpa using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, .nil, Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, .nil, Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2», Term.list]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  cases keep
  · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₂, mm,
      mv, modeT, r₁', r₂', rE', Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2»,
      Term.properList?, e00, a0]
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ (Bool.false = Bool.true ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, Or.inr ((kind_held_ne ef hl (hDs d ms) (fun e => hna (e ▸ ms))).mpr h)⟩
      · rintro ⟨ms, (h | h)⟩
        · cases h
        · exact ⟨d, ms, rfl, (kind_held_ne ef hl (hDs d ms) (fun e => hna (e ▸ ms))).mp h⟩
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, Lynx.Term.compare_self]
      obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.false lines hl hne A [] (by simp) f₁
        hT₁ errs (.atom "true") (Or.inl rfl)
      have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
          ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) ↔
          UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") [] v Bool.false w := by
        intro w; simp [UpdSemKR]
      obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
      simp only [Term.list] at rN1
      rcases hr with ⟨rfl, emp⟩ | ⟨bot, fr, sr⟩
      · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp⟩⟩
        cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inr ⟨r, rfl, fr, sr⟩⟩
        cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr] <;> split <;> simp_all
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
      obtain ⟨d0, md0⟩ := List.exists_mem_of_ne_nil val₁ v0
      obtain ⟨s0, -, rfl⟩ := hA1 d0 md0
      have KsNe : Ks ≠ [] := fun e => by have := (mKs s0).mpr md0; rw [e] at this; cases this
      have hA' : "atom" ∉ Ks := fun m => hna ((memKs _).mp m).1
      obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) hv Bool.false (mode_modeS Bool.false) Ks hA'
        subKs lines hl'
      rw [← keepOp_cOp] at rW
      have sW := wlg_sem ef hl' Bool.false (Or.inr vne) (mode_modeS Bool.false) hA' subKs KsNe
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      simp [vne', boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, rKs, rW]
      have memKs' : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
        simpa using memKs d
      rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, neR, lc, fc, sc⟩
      · simp only [↓reduceIte]
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.false lines hl hne A [] (by simp)
          Bool.true hT₁ errs (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) ↔
            UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks v Bool.false w := by
          intro w
          simp only [UpdSemKR, List.not_mem_nil, false_and, exists_false, false_or, true_and, reduceCtorEq,
            exists_const, or_false, ← sW]
          exact ⟨Or.inl, fun h => h.elim id fun ⟨_, h'⟩ => absurd h' (emp w)⟩
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
      · simp only [neR, ↓reduceIte, getMapKeys_single, lc, Option.toList]
        obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.false lines hl hne A [c]
          (by simpa using fc) Bool.true hT₁ errs (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ [c], denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) ↔
            UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks v Bool.false w := by
          intro w
          simp only [UpdSemKR, List.mem_singleton, exists_eq_left, sc, sW, reduceCtorEq, false_and, exists_false,
            or_false, true_and, KsNe, ne_eq, not_false_eq_true]
          exact or_comm
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [Term.list] at rN1; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs', Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [Term.list] at rN1; simp [rN1, rN2, rr]
  · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mm, m₃,
      modeT, r₁', r₂', rE', Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«--/2»,
      Term.properList?, e00, a0]
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs' : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ (Bool.true = Bool.true ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memKs d
    by_cases d0 : Ds = []
    · subst d0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((memKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.true lines hl hne A [] (by simp) f₁
        hT₁ errs (.atom "true") (Or.inl rfl)
      have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
          ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) ↔
          UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") [] v Bool.true w := by
        intro w; simp [UpdSemKR]
      obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
      simp only [Term.list] at rN1
      rcases hr with ⟨rfl, emp⟩ | ⟨bot, fr, sr⟩
      · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs' d, Or.inl ⟨rfl, emp⟩⟩
        cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
          simp [rN1, rN2, rr]
      · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs' d,
          Or.inr ⟨r, rfl, fr, sr⟩⟩
        cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
          simp [rN1, rN2, rr]
    · have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
      have KsNe : Ks ≠ [] := fun e => by
        obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil Ds d0
        have := (memKs d).mpr md; rw [e] at this; cases this
      have hA' : "atom" ∉ Ks := fun m => hna ((memKs _).mp m)
      obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) hv Bool.false (mode_modeS Bool.true) Ks hA'
        subKs lines hl'
      rw [← keepOp_cOp] at rW
      have sW := wlg_sem ef hl' Bool.false (Or.inr vne) (mode_modeS Bool.true) hA' subKs KsNe
      have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
        cases Ds with
        | nil => exact absurd rfl d0
        | cons _ _ => simp [Term.list]
      rcases mapsD_cases mR with ⟨rfl, emp⟩ | ⟨c, neR, lc, fc, sc⟩
      · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.true lines hl hne A [] (by simp)
          f₁ hT₁ errs (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ ([] : List Term), denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) ↔
            UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks v Bool.true w := by
          intro w
          simp only [UpdSemKR, List.not_mem_nil, false_and, exists_false, false_or, true_and, reduceCtorEq,
            exists_const, or_false, ← sW]
          exact ⟨Or.inl, fun h => h.elim id fun ⟨_, h'⟩ => absurd h' (emp w)⟩
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, rKs, rW] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, rKs, rW] at rN1 rN2 ⊢ <;>
            simp [rN1, rN2, rr]
      · obtain ⟨T', Er', f', B', rN1, rN2, fB', sB'⟩ := named_tail ef hn hv vne Bool.true lines hl hne A [c]
          (by simpa using fc) f₁ hT₁ errs (.atom "true") (Or.inl rfl)
        have sem : ∀ w, ((∃ b ∈ [c], denMF E den b w = Bool.true) ∨
            ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) ↔
            UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) A (.atom "nil") Ks v Bool.true w := by
          intro w
          simp only [UpdSemKR, List.mem_singleton, exists_eq_left, sc, sW, reduceCtorEq, false_and, exists_false,
            or_false, true_and, KsNe, ne_eq, not_false_eq_true]
          exact or_comm
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (fun w => (sB' w).trans (sem w))
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, rKs, rW, neR,
            getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, rKs, rW, neR,
            getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]

/-- `map_update_box/6` for a constant update, as the maps `BoxSem` gives. -/
theorem box_part (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (bdd : Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) (fbd : MField E bdd)
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {nt : Term} (hnt : E nt)
    (snt : nt = .atom "term" ∨ ∃ Z, nt = .map Z) (nopt : Bool) {md : String} (hmd : Mode md)
    (S ks AK : List String) (hks : ∀ s ∈ ks, s ∉ S) (hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ S)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ S ∨ s ∈ ks) (Bx : List String) (hBx : ∀ d ∈ Bx, d ∈ domainKinds)
    (hAt : "atom" ∈ Bx ∨ (md = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x))
    (hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx) :
    ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 4)) bdd (Term.list lines) (Term.list (ks.map Term.atom))
        (Term.list (Bx.map Term.atom)) (cOp nt nopt md) (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
      MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) S nt nopt md Bx) := by
  obtain ⟨NK, R, res, run, akNK, lnNK, orNK, hR, X, rfl, mX⟩ := box_runG ef hn lines bdd hl fbd sbd hnt snt nopt hmd
    ks AK Bx hBx
  exact ⟨X, run, mX.1, mX.2.1, fun w => (mX.2.2 w).trans (box_sem_iff ef hl hne S ks AK NK Bx hBx hks hAK akNK lnNK
    orNK lnKS hAt hlen hR w)⟩

/-- `map_update_widen/3` for a constant update at kinds other than atoms, as the maps `WRes` gives. -/
theorem widen_part (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {nt : Term} (hnt : E nt) (nopt : Bool)
    (hne : nopt = Bool.true ∨ ∃ x, den nt x) {md : String} (hmd : Mode md) (Ws : List String) (hA : "atom" ∉ Ws)
    (hD : ∀ d ∈ Ws, d ∈ domainKinds) (neW : Ws ≠ []) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_widen/3» (D (n + 5)) (Term.list lines) (Term.list (Ws.map Term.atom))
        (cOp nt nopt md) = .ok (.map R) ∧ MapsD E den R (WRes den (fun u => ∃ L ∈ lines, InMLine den L u) nt md Ws) := by
  obtain ⟨R, rW, mR⟩ := widen_run_gen ef hn hnt nopt hmd Ws hA hD lines hl
  exact ⟨R, rW, mR.1, mR.2.1, fun w => (mR.2.2 w).trans (wlg_sem ef hl nopt hne hmd hA hD neW w)⟩

/-- The named keys of `map_update_static_dnf/6` for `:keep` and `:reject` of a value at the atoms outside a negated
set, asking for the old values: nothing is built. -/
theorem named_tail_neg (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (hne : lines ≠ []) (ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : List Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, Term.list errs, boolAtom fl])
        (Term.list lines) (Term.list []) (keepOp v keep) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (keepOp v keep) (.atom "false") (.atom "true") (.atom "true")
        (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ ∃ b ∈ Bl, denMF E den b w = Bool.true := by
  classical
  let lk : String → Bool := fun a => decide (Lacking den lines a)
  have hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a := fun a => by simp [lk]
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, -, -, -, bT₂⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.true Bool.true lk hlk [] Bl fl T₁ (Term.list errs) hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, -, -, -, bF', -⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.false Bool.false lk hlk ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  exact ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => by rw [sB₂]; simp⟩

/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a value at the atoms outside a negated set and some kinds,
asking for the old values. -/
theorem upd_dnf_neg (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT [] (.map N) (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm v keep) := by
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
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => compareExact (x.fuel y) x y == .eq) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2», Term.list]
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl ([] ++ ks)
  have hcb : (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), .nil]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», Lynx.Except.ok_bind]
    simpa [Erlang.erlang.«++/2»] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), .nil]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), .nil]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  cases keep
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      modeT, r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, e00, a0, mk0, Erlang.sets.«to_list/1»,
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
      simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Except.tryWith, Lynx.Term.compare_self,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.false)
          [] w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemKR, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl hne
          ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false) fun w => by
            rw [sB', ← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl hne
          ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false) fun w => by
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
        simp [hL', rZ, Term.list, Lynx.Term.compare_self]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
            hne ks [] (by simp) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
              rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
            hne ks [c] (by simpa using fc) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
            (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
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
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
              (modeS Bool.false) (Ks.filter (· = "atom")) w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks v Bool.false w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
              hne ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
                rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
              hne ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
                rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
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
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
              hne ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
                rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.false lines hl
              hne ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
              (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false) fun w => by
                rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      modeT, r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, e00, a0, mk0, Erlang.sets.«to_list/1»,
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
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.true lines hl
          hne ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true) fun w => by
            rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.true lines hl
          hne ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true) fun w => by
            rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
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
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.true lines hl
          hne ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true) fun w => by
            rw [sB', ← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_neg ef hn hv vne Bool.true lines hl
          hne ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := UpdSemKR den
          (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true) fun w => by
            rw [sB', ← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]



end

end Elixir.STTDescrProofsTest.Nest
