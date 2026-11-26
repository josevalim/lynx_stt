namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The line fold of the general clause of `map_update_named_key/5` accumulates the old field, whatever the pairs. -/
theorem old_fold1 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (op : Term) :
    ∀ (lines : List Term), (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (pr F q : Term), FieldValue E F →
      Erlang.lists.«foldl_1/3» (D (n + 3)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-0-" 2
        #[.atom a, op]) (.tuple #[pr, F]) (Term.list lines) = .ok q →
      ∃ pr' F', q = .tuple #[pr', F'] ∧ FieldValue E F' ∧
        ∀ o, FieldSem den F' o ↔ FieldSem den F o ∨ ∃ L ∈ lines, LongM den L a o
  | [], _, pr, F, q, hF, h => by
    simp [Erlang.lists.«foldl_1/3»] at h
    subst h
    exact ⟨pr, F, rfl, hF, fun o => by simp⟩
  | L :: lines, hl, pr, F, q, hF, h => by
    obtain ⟨⟨tag, l, negs, rfl, g, sl, lits⟩, ne⟩ := hl L List.mem_cons_self
    obtain ⟨k, P, acc', run, hacc, sacc, -⟩ := split_line ef hn a g sl lits ne hF
    rw [Erlang.lists.«foldl_1/3».eq_def] at h
    simp only at h
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-0-/2».pure] at h
    obtain ⟨s, hs, h⟩ := bind_ok h
    simp only [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-0-/4», run, Lynx.Except.ok_bind] at hs
    obtain ⟨np, -, hs⟩ := bind_ok hs
    obtain ⟨rv, -, hs⟩ := bind_ok hs
    cases hs
    obtain ⟨pr', F', rfl, hF', sF'⟩ := old_fold1 ef hn a op lines (fun L' mL => hl L' (List.mem_cons_of_mem _ mL))
      rv acc' q hacc h
    refine ⟨pr', F', rfl, hF', fun o => ?_⟩
    rw [sF', sacc]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨L', mL, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, Or.inl rfl, h⟩
      · exact Or.inr ⟨L', Or.inr mL, h⟩
    · rintro (h | ⟨L', rfl | mL, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨L', mL, h⟩

/-- The general clause of `map_update_named_key/5` for a constant with `:keep` or `:reject`: whatever the updated
maps, the old field holds the values at the key of the maps of the lines. -/
theorem general_old (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (c : Term) (md : String)
    (hmd : md = "keep" ∨ md = "reject")
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ow r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", c], .atom md]) (.atom "true") ow = .ok r) :
    ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5» at h
  rcases hmd with e | e <;> simp [e] at h
  all_goals
    obtain ⟨p, hp, h⟩ := bind_ok h
    have hr : ∃ b, r = .tuple #[b, p.2] := by
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      cases h; exact ⟨_, rfl⟩
    obtain ⟨b, rfl⟩ := hr
    refine ⟨b, p.2, rfl, ?_⟩
    split at hp
    · rename_i fs heq
      obtain ⟨L, rfl⟩ : ∃ L, lines = [L] := by
        rcases lines with _ | ⟨L, _ | ⟨L', rest⟩⟩
        · simp [Term.list] at heq
        · exact ⟨L, rfl⟩
        · simp [Term.list] at heq
      simp only [Term.list, Term.cons.injEq, and_true] at heq
      subst heq
      obtain ⟨⟨tag, l, negs, eL, g, sl, -⟩, ⟨w₀, hw₀⟩⟩ := hl _ List.mem_cons_self
      obtain ⟨rfl, rfl, en⟩ := tuple3_inj eL
      obtain rfl : negs = [] := by cases negs with | nil => rfl | cons x xs => simp [Term.list] at en
      obtain ⟨k, rpop, -, -, -⟩ := pop_pair (den := den) ef g sl a
      rw [rpop] at hp
      simp only [Lynx.Except.ok_bind] at hp
      obtain ⟨_, _, hp⟩ := bind_ok hp
      cases hp
      have h₀ := (inMLine_iff (negs := []) .. |>.mp hw₀).1
      refine ⟨fieldAt_ok ef g sl a, fun o => ?_⟩
      rw [lit_values ef g a h₀ o]
      simp only [List.mem_singleton, exists_eq_left, LongM]
      exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
        fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩
    · obtain ⟨q, hq, hp⟩ := bind_ok hp
      have hq' : Erlang.lists.«foldl_1/3» (D (n + 3)) (.function false "Elixir.Module.Types.Descr"
          "-map_update_named_key/5-fun-0-" 2 #[.atom a, .tuple #[.tuple #[.atom "constant", c], .atom md]])
          (.tuple #[.nil, .tuple #[.map [], .atom "false"]]) (Term.list lines) = .ok q := by
        rcases lines with _ | ⟨L, rest⟩ <;>
          simp_all [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list, Erlang.lists.«foldl_1/3»]
      obtain ⟨pr', F', rfl, hF', sF'⟩ := old_fold1 ef hn a _ lines hl .nil _ q (none_field ef).1 hq'
      obtain ⟨_, _, hp⟩ := bind_ok hp
      cases hp
      refine ⟨hF', fun o => ?_⟩
      rw [sF']
      simp [(none_field (den := den) ef).2 o]

/-- `map_update_named_keys/8` for a constant, asking for the old values: when it succeeds, the old values united with
those at the keys. -/
theorem named_val (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (c : Term) (md : String)
    (hmd : md = "force" ∨ md = "keep" ∨ md = "reject") (req st bd : Term)
    (hk : ∀ a r, Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", c], .atom md]) bd (.atom "true") = .ok r →
      ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) :
    ∀ (ks : List String) (T B Er F r : Term), E T →
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, B, Er, F]) (Term.list lines)
        (Term.list (ks.map Term.atom)) (.tuple #[.tuple #[.atom "constant", c], .atom md]) req st (.atom "true") bd =
        .ok r →
      ∃ T' B' Er' F', r = .tuple #[T', B', Er', F'] ∧ E T' ∧
        ∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x) := by
  have loop : ∀ (fc : Term), (fc = .atom "true" ∨ fc = .atom "false") →
      (fc = .atom "true" ↔ md = "force") → ∀ (ks : List String) (T B Er F r : Term), E T →
      Erlang.lists.«foldl_1/3» (D (n + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
          #[Term.list lines, .tuple #[.tuple #[.atom "constant", c], .atom md], req, st, bd, .atom "true", fc])
        (.tuple #[T, B, Er, F]) (Term.list (ks.map Term.atom)) = .ok r →
      ∃ T' B' Er' F', r = .tuple #[T', B', Er', F'] ∧ E T' ∧
        ∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x) := by
    intro fc hfc efc ks
    induction ks with
    | nil =>
      intro T B Er F r hT h
      simp [Erlang.lists.«foldl_1/3», Term.list] at h
      subst h
      exact ⟨T, B, Er, F, rfl, hT, by simp⟩
    | cons a rest ih =>
      intro T B Er F r hT h
      rw [Erlang.lists.«foldl_1/3».eq_def] at h
      simp only [Term.list, List.map] at h
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at h
      obtain ⟨acc, hs, h⟩ := bind_ok h
      simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at hs
      obtain ⟨r₀, h₀, hs⟩ := bind_ok hs
      obtain ⟨bdds, Fa, rfl, hFa, sFa⟩ := hk a r₀ h₀
      obtain ⟨t, o, rfl, ht⟩ := hFa
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      have step : ∃ T'' x y z, acc = .tuple #[T'', x, y, z] ∧ E T'' ∧
          ∀ x, den T'' x ↔ den T x ∨ ∃ L ∈ lines, LongM den L a (some x) := by
        have someE : ∀ x, den t x ↔ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
          rw [← sFa, fieldSem_mk]; simp
        have sU : ∀ x, den u x ↔ den T x ∨ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
          rw [su, someE]; exact or_comm
        have sT0 : e = Bool.true → ∀ x, den T x ↔ den T x ∨ ∃ L ∈ lines, LongM den L a (some x) := fun he x =>
          ⟨Or.inl, fun h => h.elim id fun h' => absurd ((someE x).mpr h') (se.mp he x)⟩
        obtain ⟨B', -, hs⟩ := bind_ok hs
        rcases hfc with rfl | rfl
        · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru] at hs
          repeat' (first | (obtain ⟨_, -, hs⟩ := bind_ok hs) | split at hs)
          all_goals first | (cases hs; exact ⟨u, _, _, _, rfl, hu, sU⟩) | (cases hs) | skip
        · cases e
          · simp [re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom] at hs
            repeat' (first | (obtain ⟨_, -, hs⟩ := bind_ok hs) | split at hs)
            all_goals first | (cases hs; exact ⟨u, _, _, _, rfl, hu, sU⟩) | (cases hs) | skip
          · simp [re, Lynx.Term.isMember, boolAtom] at hs
            repeat' (first | (obtain ⟨_, -, hs⟩ := bind_ok hs) | split at hs)
            all_goals first | (cases hs; exact ⟨T, _, _, _, rfl, hT, sT0 rfl⟩) | (cases hs) | skip
      obtain ⟨T'', x, y, z, rfl, hT'', sT''⟩ := step
      obtain ⟨T', B', Er', F', rfl, hT', sT'⟩ := ih T'' x y z r hT'' h
      refine ⟨T', B', Er', F', rfl, hT', fun x => ?_⟩
      rw [sT', sT'']
      simp only [List.mem_cons]
      constructor
      · rintro ((hh | hh) | ⟨a', ma, hh⟩)
        · exact Or.inl hh
        · exact Or.inr ⟨a, Or.inl rfl, hh⟩
        · exact Or.inr ⟨a', Or.inr ma, hh⟩
      · rintro (hh | ⟨a', rfl | ma, hh⟩)
        · exact Or.inl (Or.inl hh)
        · exact Or.inl (Or.inr hh)
        · exact Or.inr ⟨a', ma, hh⟩
  intro ks T B Er F r hT h
  have fcE : ∃ fc, (fc = Term.atom "true" ∨ fc = .atom "false") ∧ (fc = .atom "true" ↔ md = "force") ∧
      Erlang.erlang.«==/2» (.atom md) (.atom "force") = .ok fc := by
    rcases hmd with rfl | rfl | rfl <;> simp [Erlang.erlang.«==/2»]
  obtain ⟨fc, hfc, efc, rfc⟩ := fcE
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2»] at h
  simp [Lynx.Except.orElse, Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», rfc] at h
  rcases ks with _ | ⟨k, t⟩
  · simp [Term.list] at h
    subst h
    exact ⟨T, B, Er, F, rfl, hT, by simp⟩
  · apply loop fc hfc efc (k :: t) T B Er F r hT
    simp only [Term.list, List.map] at h ⊢
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simpa using h

/-- `map_update_named_key/5` deleting a key, building or not, asking for the old field. -/
theorem del_key (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (md : String) (hmd : md = "force" ∨ md = "keep" ∨ md = "reject")
    (bd : Bool) (a : String) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md]) (boolAtom bd) (.atom "true") =
      .ok r) :
    ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember, rF] at h
    exact ⟨_, F, h.symm, hF, sF⟩
  · rcases hmd with rfl | hmd
    · obtain ⟨ba, rba, -, -⟩ := put_lines ef hn a (leafPut_del ef a) lines hl
      have := rba Bool.true F fun _ => rF
      simp only [boolAtom, ite_true] at this h
      rw [this] at h
      cases h
      exact ⟨_, F, rfl, hF, sF⟩
    · exact general_old ef hn a _ md hmd lines hl _ r (by simpa [boolAtom] using h)

/-- `map_update_static_dnf/6` for a constant, asking for the old values: when it succeeds, the old values are the values
at the keys. -/
theorem dnf_val (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) (md : String)
    (hmd : md = "force" ∨ md = "keep" ∨ md = "reject") (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk : List String)
    (neg : Term) (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hRk : R = [] ∨ rk = [])
    (hk : ∀ (bd : Bool) a r, Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") = .ok r →
      ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (.atom "true") = .ok r) :
    ∃ T Y er f, r = .tuple #[T, Y, er, f] ∧ E T ∧
      ∀ x, den T x ↔ (∃ s ∈ Ds, ∃ L ∈ lines, LineTag den L s x) ∨
        ∃ a, (a ∈ rk ∨ a ∈ R) ∧ ∃ L ∈ lines, LongM den L a (some x) := by
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
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (rk ++ R)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (R.map Term.atom), Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  have sem : ∀ T' T'' : Term, (∀ x, den T' x ↔ den T₁ x ∨ ∃ a ∈ rk, ∃ L ∈ lines, LongM den L a (some x)) →
      (∀ x, den T'' x ↔ den T' x ∨ ∃ a ∈ R, ∃ L ∈ lines, LongM den L a (some x)) →
      ∀ x, den T'' x ↔ (∃ s ∈ Ds, ∃ L ∈ lines, LineTag den L s x) ∨
        ∃ a, (a ∈ rk ∨ a ∈ R) ∧ ∃ L ∈ lines, LongM den L a (some x) := fun T' T'' s' s'' x => by
    rw [s'', s', sT₁]
    simp only [ef.den_none x, false_or]
    constructor
    · rintro ((hy | ⟨a, ma, hh⟩) | ⟨a, ma, hh⟩)
      · exact Or.inl hy
      · exact Or.inr ⟨a, Or.inl ma, hh⟩
      · exact Or.inr ⟨a, Or.inr ma, hh⟩
    · rintro (hy | ⟨a, ma | ma, hh⟩)
      · exact Or.inl (Or.inl hy)
      · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
      · exact Or.inr ⟨a, ma, hh⟩
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h
  simp only [splitT] at h
  rcases hmd with rfl | rfl | rfl <;>
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃, mv,
      r₁', r₂', rE', Lynx.Except.andAlso] at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok h
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
      (hk Bool.true) rk _ _ _ _ _ hT₁ h97
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h
    obtain ⟨r5, h5, h⟩ := bind_ok h
    obtain ⟨T'', B'', Er'', F'', rfl, hT'', sT''⟩ := named_val ef (n := n + 2) (by omega) lines fld _ (by simp) _ _ _
      (hk bd) R _ _ _ _ _ hT' h5
    obtain ⟨u, -, h⟩ := bind_ok h
    split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)


/-- `dnf_val` on the lines of a map field: the old values are the values `map_get/2` selects. -/
theorem dnf_val_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) (md : String)
    (hmd : md = "force" ∨ md = "keep" ∨ md = "reject")
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a r,
      Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5)) (Term.list lines) (.atom a)
        (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") = .ok r →
      ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (_hne : lines ≠ []) (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String}
    {neg : Term} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (.atom "true") = .ok r) :
    ∃ T Y er f, r = .tuple #[T, Y, er, f] ∧ E T ∧
      ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
        w κ = some x := by
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split (den := den) ef fb (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_of fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  have hRk : R' = [] ∨ rk = [] := by
    cases R' with
    | nil => exact Or.inl rfl
    | cons r rs =>
      obtain ⟨s, -, N, eN, -⟩ := hR _ List.mem_cons_self
      exact Or.inr (nr N eN)
  obtain ⟨T, Y, er, f, rfl, hT, sT⟩ := dnf_val ef hn fld md hmd b lines hl rk neg Ds
    (fun s ms => by obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms') R' rR hRk
    (hkL lines hl) r h
  refine ⟨T, Y, er, f, rfl, hT, fun x => ?_⟩
  rw [sT, ← pieces_sem ef lines hl sl ok hR swR x]
  simp only [List.mem_map, Term.atom.injEq, exists_eq_right]
  constructor
  · rintro (⟨s, ms, hh⟩ | ⟨a, ma | ma, hh⟩)
    · exact Or.inr ⟨s, ms, hh⟩
    · exact Or.inl (Or.inl ⟨a, ma, hh⟩)
    · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
  · rintro ((⟨a, ma, hh⟩ | ⟨a, ma, hh⟩) | ⟨s, ms, hh⟩)
    · exact Or.inr ⟨a, Or.inl ma, hh⟩
    · exact Or.inr ⟨a, Or.inr ma, hh⟩
    · exact Or.inl ⟨s, ms, hh⟩

/-- `map_update_static/5` for `:keep` and `:reject` of a static value at a split of static keys, asking for the old
values: `:badmap`, or the values `map_get/2` selects as old values. -/
theorem val_old_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) (md : String)
    (hmd : md = "force" ∨ md = "keep" ∨ md = "reject")
    (hkL : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → ∀ (bd : Bool) a r,
      Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5)) (Term.list lines) (.atom a)
        (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") = .ok r →
      ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (res : Term)
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (.atom "true") (.atom "true") = .ok res) :
    res = .atom "badmap" ∨ ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧ E T ∧
      ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
        w κ = some x := by
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
      obtain ⟨T, Y, er, f, e, hT, sT⟩ := dnf_val_sem ef hn fld md hmd hkL fb _ hl (by simp) inB ok nr res run
      exact Or.inr ⟨T, Y, er, f, e, ⟨w₀, (sem w₀).mpr h₀⟩, hT, sT⟩
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
      obtain ⟨T, Y, er, f, e, hT, sT⟩ := dnf_val_sem ef hn fld md hmd hkL fb _ hl (by simp) inB ok nr res run
      exact Or.inr ⟨T, Y, er, f, e, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hT, sT⟩


end

section
variable {t : Term} {n : Nat}

/-- `map_update/5` for `:keep` and `:reject` of a static value at a static key type, asking for the old values, in
static types of the next level: `:badmap`, an error, or the values `map_get/2` selects as old values. -/
theorem update_delete_old {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (md : String) (hmd : md = "force" ∨ md = "keep" ∨ md = "reject")
    (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
      .ok r) :
    r = .atom "badmap" ∨ (∃ er, r = .tuple #[.atom "error", er]) ∨
      ∃ T Y er, r = .tuple #[T, Y, er] ∧ MOnly t n X ∧ (level t n).E T ∧
        ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
          w κ = some x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D (k + 6)) (.map X) key (.atom "delete") (.atom md)
      (.atom "true") = Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
        (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md]) (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«map_update/5»
    rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk]
  rw [upd] at run
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
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md]) (.atom "true")
          (.atom "true") with
      | error e => simp [key, mo, hs, Lynx.Except.andAlso] at run
      | ok res =>
        rcases val_old_static (level t n).ef (n := k) (by omega) _ md hmd
          (fun lines hl bd a r h => del_key (level t n).ef (n := k + 2) (by omega) lines hl md hmd bd a r h) ok nr hb fb
          res hs with
          rfl | ⟨T, Y, er, f, rfl, ⟨w₀, hw₀⟩, hT, sT⟩
        · left
          simp [key, mo, hs, Lynx.Except.andAlso,
            Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
            Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
          exact run.symm
        · simp [key, mo, hs, Lynx.Except.andAlso] at run
          split at run
          · right; left; simp at run; exact ⟨er, run.symm⟩
          · right; right
            simp at run
            exact ⟨T, Y, er, run.symm, only.mpr ⟨restE, w₀, hw₀⟩, hT, fun x => by rw [sT]; simp only [mt]⟩
    · rw [bp_false.mpr restE] at mo
      left
      simp [key, mo, Lynx.Except.andAlso, boolAtom,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure,
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»] at run
      exact run.symm

end

end Elixir.STTDescrProofsTest.Nest
