namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The operation of `:keep` and `:reject` of a constant. -/
abbrev keepOp (v : Term) (keep : Bool) : Term := .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]

/-- Keys some map of the lines lacks. -/
def Lacking (den : Term → V → Prop) (lines : List Term) (a : String) : Prop := ∃ L ∈ lines, LongM den L a none

/-- The maps of an update at a key with `:keep` or `:reject`: those whose key held a value, with a value of the type,
and with `:keep`, those without the key. -/
def KeepSem (den : Term → V → Prop) (v : Term) (keep : Bool) (lines : List Term) (a : String) (w : MW V) : Prop :=
  (PutAt den v a w ∧ ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
    (keep = Bool.true ∧ w (.atom a) = none ∧ ∃ L ∈ lines, InMLine den L w)

/-- `map_update_named_keys/8` for `:keep` and `:reject` of a constant, asking for the old values, on a static type: the
old values united with those at the keys, `badkey` for the required keys some map lacks, and found when some key no
map lacks. -/
theorem named_keep (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (req bd : Bool)
    (lk : String → Bool) (hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a) :
    ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, Term.list B, Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (keepOp v keep) (boolAtom req) (.atom "true") (.atom "true")
          (boolAtom bd) = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x)) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ ∃ a ∈ ks, ¬Lacking den lines a) ∧
        (∀ Er₀ : List Term, Er = Term.list Er₀ → Er' = Term.list
          ((if req then (ks.filter lk).reverse.map
            (fun a => Term.tuple #[.atom "badkey", .atom a]) else []) ++ Er₀)) ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, KeepSem den v keep lines a w) := by
  classical
  have loop : ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, keepOp v keep, boolAtom req, .atom "true", boolAtom bd, .atom "true", .atom "false"])
          (.tuple #[T, Term.list B, Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (∀ x, den T' x ↔ den T x ∨ ∃ a ∈ ks, ∃ L ∈ lines, LongM den L a (some x)) ∧
        (f' = Bool.true ↔ f = Bool.true ∨ ∃ a ∈ ks, ¬Lacking den lines a) ∧
        (∀ Er₀ : List Term, Er = Term.list Er₀ → Er' = Term.list
          ((if req then (ks.filter lk).reverse.map
            (fun a => Term.tuple #[.atom "badkey", .atom a]) else []) ++ Er₀)) ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, KeepSem den v keep lines a w) := by
    intro ks
    induction ks with
    | nil =>
      intro B f T Er hT
      exact ⟨B, f, T, Er, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, by simp, by simp, fun Er₀ e => by
        subst e; cases req <;> simp, fun _ => rfl, fun _ fB => ⟨fB, fun w => by simp⟩⟩
    | cons a rest ih =>
      intro B f T Er hT
      -- The old field at the key, and the maps of its update.
      obtain ⟨ba, F, rb, hF, sF, bF, bT⟩ : ∃ (ba : List Term) (F : Term),
          Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a) (keepOp v keep)
            (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
          (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧ (bd = Bool.false → ba = []) ∧
          (bd = Bool.true → (∀ b ∈ ba, MField E b) ∧
            ∀ w, (∃ b ∈ ba, denMF E den b w = Bool.true) ↔ KeepSem den v keep lines a w) := by
        cases bd
        · obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
          exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
            Term.list, rF], hF, sF, fun _ => rfl, fun h => (by cases h)⟩
        · obtain ⟨ba, F, rb, fba, hF, sF, sba⟩ := keep_lines ef hn a hv vne keep lines hl (.atom "true")
          exact ⟨ba, F, rb, hF, sF, fun h => (by cases h), fun _ => ⟨fba, sba⟩⟩
      obtain ⟨t, o, rfl, ht⟩ := hF
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      have optE : o = Bool.true ↔ Lacking den lines a := by
        rw [Lacking, ← sF, fieldSem_mk]; simp
      have someE : ∀ x, den t x ↔ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
        rw [← sF, fieldSem_mk]; simp
      -- An empty old type means some map lacks the key.
      have eo : e = Bool.true → o = Bool.true := fun he => by
        obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
        obtain ⟨w, hw⟩ := (hl L mL).2
        cases wa : w (.atom a) with
        | none => exact optE.mpr ⟨L, mL, w, hw, wa⟩
        | some x => exact absurd ((someE x).mpr ⟨L, mL, w, hw, wa⟩) (se.mp he x)
      have lkE : lk a = o := by
        cases h : lk a <;> cases o
        · rfl
        · exact absurd ((hlk a).mpr (optE.mp rfl)) (by simp [h])
        · exact absurd (optE.mpr ((hlk a).mp h)) (by simp)
        · rfl
      obtain ⟨B', f', T', Er', r₁, hT', sT', fT', eT', bF', bT'⟩ := ih (ba ++ B) (f || !o) (if e then T else u)
        (if req && o then .cons (.tuple #[.atom "badkey", .atom a]) Er else Er) (by cases e <;> simp [hT, hu])
      refine ⟨B', f', T', Er', ?_, hT', fun x => ?_, ?_, fun Er₀ eE => ?_, fun hb => ?_, fun hb fB => ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
            (keepOp v keep) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) := rb
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb']
        cases e
        · cases o <;> cases req <;> cases f <;>
            simp [re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom, Lynx.Except.andAlso,
              Lynx.Except.orElse, Erlang.erlang.«not/1», append_list] at r₁ ⊢ <;> exact r₁
        · obtain rfl := eo rfl
          cases req <;> cases f <;>
            simp [re, Lynx.Term.isMember, boolAtom, append_list] at r₁ ⊢ <;> exact r₁
      · rw [sT']
        simp only [List.mem_cons]
        have hx : den (if e then T else u) x ↔ den T x ∨ ∃ L ∈ lines, LongM den L a (some x) := by
          cases e
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [su, someE]; exact or_comm
          · simp only [↓reduceIte]
            exact ⟨Or.inl, fun h => h.elim id fun h' => absurd ((someE x).mpr h') (se.mp rfl x)⟩
        rw [hx]
        constructor
        · rintro ((h | h) | ⟨a', ma, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, Or.inl rfl, h⟩
          · exact Or.inr ⟨a', Or.inr ma, h⟩
        · rintro (h | ⟨a', rfl | ma, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨a', ma, h⟩
      · rw [fT']
        simp only [List.mem_cons, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        constructor
        · rintro ((h | h) | ⟨a', ma, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, Or.inl rfl, fun hl => by rw [← optE] at hl; simp [hl] at h⟩
          · exact Or.inr ⟨a', Or.inr ma, h⟩
        · rintro (h | ⟨a', rfl | ma, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (by cases o <;> first | rfl | exact absurd (optE.mp rfl) h))
          · exact Or.inr ⟨a', ma, h⟩
      · subst eE
        have e₁ : (if req && o then Term.cons (.tuple #[.atom "badkey", .atom a]) (Term.list Er₀) else Term.list Er₀) =
            Term.list ((if req && o then [Term.tuple #[.atom "badkey", .atom a]] else []) ++ Er₀) := by
          cases req <;> cases o <;> rfl
        rw [eT' _ e₁]
        cases req <;> simp [List.filter_cons, lkE] <;> cases o <;> simp
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
  obtain ⟨B', f', T', Er', r₁, hT', sT', fT', eT', bF', bT'⟩ := loop ks B f T Er hT
  refine ⟨B', f', T', Er', ?_, hT', sT', fT', eT', bF', bT'⟩
  cases keep
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, modeT]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      exact r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa using r₁

/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a constant at a split of static keys, asking for the old
values: the values at the keys. -/
theorem dnf_keep_old (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) (rk : List String)
    (neg : Term) (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hRk : R = [] ∨ rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok r) :
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
  let lk : String → Bool := fun a => decide (Lacking den lines a)
  have hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a := fun a => by simp [lk]
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
  cases keep
  · simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂,
      mv, modeT, r₁', r₂', rE'] at h
    rcases val₁ with _ | ⟨d₀, rest₀⟩
    · cases f₁
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.false T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.false) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.false) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.true T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.false) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.false) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
    · cases f₁
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.false T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.false) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.false) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.true T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.false) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.false lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.false) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
  · simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂,
      m₃, modeT, r₁', r₂', rE'] at h
    rcases Ds with _ | ⟨d₀, rest₀⟩
    · cases f₁
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.false T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.true) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.true) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.true T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.true) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.true) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
    · cases f₁
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.false T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "false"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.true) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.true) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)
      · simp [boolAtom, Lynx.Except.orElse, Term.list] at h
        obtain ⟨X, hX, h⟩ := bind_ok h
        have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
          clear h
          simp only [bind, Except.bind, Except.tryWith] at hX
          repeat' split at hX
          all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
          all_goals done
        obtain ⟨B96, hB, h⟩ := bind_ok h
        obtain ⟨Bl, rfl⟩ : ∃ Bl : List Term, B96 = Term.list Bl := by
          clear h
          split at hB
          · obtain ⟨y, -, hB⟩ := bind_ok hB; cases hB; exact ⟨[y], rfl⟩
          · cases hB; exact ⟨[], rfl⟩
          · cases hB
        obtain ⟨B', f', T', Er', e0, hT', sT', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.true Bool.true lk hlk rk Bl Bool.true T₁ (Term.list errs) hT₁
        have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T₁, Term.list Bl, Term.list errs, .atom "true"]) (Term.list lines) (Term.list (rk.map Term.atom))
            (keepOp v Bool.true) (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
            .ok (.tuple #[T', Term.list B', Er', boolAtom f']) := by simpa using e0
        rw [e0'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
          rcases hb with hb | hb
          · exact ⟨Bool.false, hb⟩
          · exact ⟨Bool.true, hb⟩
        rw [ebd] at h
        obtain ⟨B'', f'', T'', Er'', e2, hT'', sT'', -, -⟩ := named_keep ef (n := n + 2) (by omega) hv vne Bool.true lines hl hne
          Bool.false bd lk hlk R B' f' T' Er' hT'
        have e2' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
            (.tuple #[T', Term.list B', Er', boolAtom f']) (Term.list lines) (Term.list (R.map Term.atom))
            (keepOp v Bool.true) (.atom "false") (.atom "true") (.atom "true") (boolAtom bd) =
            .ok (.tuple #[T'', Term.list B'', Er'', boolAtom f'']) := e2
        rw [e2'] at h; simp only [Lynx.Except.ok_bind] at h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)

-- end dnf_keep_old

/-- The maps of an update at a key with `:keep` or `:reject`, on the maps of a map field. -/
def KeepB (E : Term → Prop) (den : Term → V → Prop) (v : Term) (keep : Bool) (b : Term) (a : String) (w : MW V) :
    Prop :=
  (PutAt den v a w ∧ ∃ x, denMF E den b (setK a (some x) w) = Bool.true) ∨
    (keep = Bool.true ∧ w (.atom a) = none ∧ denMF E den b w = Bool.true)

/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a constant at a list of atoms, asking for the old values:
the updates at each atom, `badkey` for the atoms some map lacks, found when some atom no map lacks, and the values at
the atoms. -/
theorem keep_atoms_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ []) (A : List String)
    (lk : String → Bool) (hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a) :
    ∃ (T Y : Term) (f : Bool), Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true")
        (.atom "true") = .ok (.tuple #[T, Y,
          Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f]) ∧
      ((Y = .map [] ∧ ∀ w, ¬∃ a ∈ A, KeepSem den v keep lines a w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧
          ∀ w, denMF E den r w = Bool.true ↔ ∃ a ∈ A, KeepSem den v keep lines a w) ∧ E T ∧
      (∀ x, den T x ↔ ∃ a ∈ A, ∃ L ∈ lines, LongM den L a (some x)) ∧
      (f = Bool.true ↔ ∃ a ∈ A, ¬Lacking den lines a) := by
  obtain ⟨B', f', T', Er', e0, hT', sT', fT', eT', -, bT'⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines
    hl hne Bool.true Bool.true lk hlk A [] Bool.false (.map []) .nil ef.none
  obtain ⟨fB', sB'⟩ := bT' rfl (by simp)
  have eE := eT' [] rfl
  simp only [ite_true, List.append_nil] at eE
  subst eE
  obtain ⟨B'', f'', T'', Er'', e1, -, sT'', fT'', eT'', bF'', -⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep
    lines hl hne Bool.false Bool.true lk hlk [] B' f' T' (Term.list ((A.filter lk).reverse.map
      fun a => Term.tuple #[.atom "badkey", .atom a])) hT'
  have e1' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6))
      (.tuple #[T', Term.list B', Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]),
        boolAtom f']) (Term.list lines) .nil (keepOp v keep) (.atom "false") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T', Term.list B', Term.list ((A.filter lk).reverse.map
          fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f']) := by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse]
  have e0' : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[.map [], .nil, .nil, .atom "false"])
      (Term.list lines) (Term.list (A.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") (.atom "true")
      (.atom "true") = .ok (.tuple #[T', Term.list B', Term.list ((A.filter lk).reverse.map
          fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f']) := by simpa using e0
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 6) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ B' (Nat.le_refl _) fun b mb => ⟨fB' b mb, by
      rcases fB' b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have sem : ∀ w, denMF E den r w = Bool.true ↔ ∃ a ∈ A, KeepSem den v keep lines a w := fun w => by
    rw [sr, sB']; simp
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have mm : Erlang.erlang.«--/2» .nil (Term.list (A.map Term.atom)) = .ok .nil := by
    simp [Erlang.erlang.«--/2», Term.properList?, e00, Term.list]
  have mm0 : Erlang.erlang.«--/2» .nil .nil = .ok .nil := by simp [Erlang.erlang.«--/2», Term.properList?, Term.list]
  have run : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true")
      (.atom "true") = (Elixir.Module.Types.Descr.«map_union_all/1» (D (n + 6)) (Term.list B') >>= fun u =>
        match u with
        | .atom "bdd_bot" => .ok (.tuple #[T', .map [],
            Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f'])
        | u => .ok (.tuple #[T', .map [(.atom "map", u)],
            Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f'])) := by
    unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
    cases keep <;>
    simp [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
      Lynx.Term.isMember, mm, mm0, Erlang.erlang.«++/2»,
      Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
      Erlang.lists.«map/2», Lynx.Except.orElse, Lynx.Except.andAlso, modeT, keepOp]
    all_goals
      have e0'' := e0'
      have e1'' := e1'
      simp only [keepOp, modeT, Bool.false_eq_true, ↓reduceIte] at e0'' e1''
      rw [e0'']
      simp only [Lynx.Except.ok_bind]
      rw [e1'']
      simp only [Lynx.Except.ok_bind, List.map_reverse]
      rfl
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    refine ⟨T', .map [], f', by rw [run, rr]; rfl, Or.inl ⟨rfl, fun w h => by have := (sem w).mpr h; simp [denMF_bot] at this⟩,
      hT', fun x => by rw [sT']; simp [ef.den_none x], by rw [fT']; simp⟩
  · refine ⟨T', .map [(.atom "map", r)], f', ?_, Or.inr ⟨r, rfl, fr, sem⟩, hT', fun x => by rw [sT']; simp [ef.den_none x],
      by rw [fT']; simp⟩
    rw [run, rr]
    simp only [Lynx.Except.ok_bind]

/-- `keep_atoms_dnf` on the lines of a map field, stated on its maps. -/
theorem keep_atoms_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) {b : Term} (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (A : List String)
    (lk : String → Bool) (hlk : ∀ a, lk a = Bool.true ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) :
    ∃ (T Y : Term) (f : Bool), Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true")
        (.atom "true") = .ok (.tuple #[T, Y,
          Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f]) ∧
      ((Y = .map [] ∧ ∀ w, ¬∃ a ∈ A, KeepB E den v keep b a w) ∨
        ∃ r, Y = .map [(.atom "map", r)] ∧ MField E r ∧
          ∀ w, denMF E den r w = Bool.true ↔ ∃ a ∈ A, KeepB E den v keep b a w) ∧ E T ∧
      (∀ x, den T x ↔ ∃ a ∈ A, ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = some x) ∧
      (f = Bool.true ↔ ∃ a ∈ A, ¬∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) := by
  have lac : ∀ a, Lacking den lines a ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none := fun a =>
    longM_iff sl a none
  have keepE : ∀ a w, KeepSem den v keep lines a w ↔ KeepB E den v keep b a w := fun a w => by
    simp only [KeepSem, KeepB, sl]
    constructor
    · rintro (⟨p, L, mL, x, h⟩ | ⟨hk, hn, L, mL, h⟩)
      · exact Or.inl ⟨p, x, L, mL, h⟩
      · exact Or.inr ⟨hk, hn, L, mL, h⟩
    · rintro (⟨p, x, L, mL, h⟩ | ⟨hk, hn, L, mL, h⟩)
      · exact Or.inl ⟨p, L, mL, x, h⟩
      · exact Or.inr ⟨hk, hn, L, mL, h⟩
  obtain ⟨T, Y, f, run, hY, hT, sT, sf⟩ := keep_atoms_dnf ef hn hv vne keep b lines hl hne A lk
    (fun a => (hlk a).trans (lac a).symm)
  refine ⟨T, Y, f, run, ?_, hT, fun x => by rw [sT]; simp only [longM_iff sl], by rw [sf]; simp only [lac]⟩
  rcases hY with ⟨e, h⟩ | ⟨r, e, fr, sr⟩
  · exact Or.inl ⟨e, fun w ⟨a, ma, k⟩ => h w ⟨a, ma, (keepE a w).mpr k⟩⟩
  · exact Or.inr ⟨r, e, fr, fun w => by rw [sr]; simp only [keepE]⟩

/-- The old values of `map_update_static_dnf/6` for `:keep` and `:reject` on the non-empty lines of a map field are the
values `map_get/2` selects. -/
theorem dnf_keep_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    (keep : Bool) {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (hne : lines ≠ []) (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String}
    {neg : Term} (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok r) :
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
  obtain ⟨T, Y, er, f, rfl, hT, sT⟩ := dnf_keep_old ef hn hv vne keep b lines hl hne rk neg Ds
    (fun s ms => by obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms') R' rR hRk r h
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
theorem keep_old_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (res : Term)
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok res) :
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
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) (splitT (rk.map Term.atom) neg (Ds.map Term.atom))
            (keepOp v keep) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      rw [unf] at run
      obtain ⟨T, Y, er, f, e, hT, sT⟩ := dnf_keep_sem ef hn hv vne keep fb _ hl (by simp) inB ok nr res run
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
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest))
            (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      rw [unf] at run
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      obtain ⟨T, Y, er, f, e, hT, sT⟩ := dnf_keep_sem ef hn hv vne keep fb _ hl (by simp) inB ok nr res run
      exact Or.inr ⟨T, Y, er, f, e, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hT, sT⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_update/5` for `:keep` and `:reject` of a static value at a static key type, asking for the old values, in
static types of the next level: `:badmap`, an error, or the values `map_get/2` selects as old values. -/
theorem update_keep_old {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    {v : Term} (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) (keep : Bool)
    (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (modeT keep) (.atom "true") = .ok r) :
    r = .atom "badmap" ∨ (∃ er, r = .tuple #[.atom "error", er]) ∨
      ∃ T Y er, r = .tuple #[T, Y, er] ∧ MOnly t n X ∧ (level t n).E T ∧
        ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧
          w κ = some x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D (k + 6)) (.map X) key v (modeT keep) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«map_update/5»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk,
        Lynx.Term.getMapKeys, modeT, keepOp]
    · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk,
        getMapKeys_single, sZ, modeT, keepOp]
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
          (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") with
      | error e => simp [key, mo, hs, Lynx.Except.andAlso] at run
      | ok res =>
        rcases keep_old_static (level t n).ef (n := k) (by omega) hv vne keep ok nr hb fb res hs with
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

section
variable {t : Term} {n : Nat}

/-- The required atoms of the split of a static key type are distinct. -/
theorem split_nodup {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} {rs : List Term} {neg : Term}
    {ds : List Term}
    (h : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map Y) = .ok (splitT rs neg ds)) :
    rs.Nodup := by
  have st := (de_map hY).static
  rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def] at h
  cases ha : mapLookup Y (.atom "atom") with
  | none =>
    simp [getMapKeys_single, st, ha, splitT] at h
    cases hd : Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) with
    | error e => rw [hd] at h; cases h
    | ok x =>
      rw [hd] at h
      simp only [Lynx.Except.ok_bind, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at h
      have e := list_inj (show Term.list [] = Term.list rs from h.1)
      subst e; simp
  | some x =>
    obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map hY).fields _ _ ha)
    cases pos
    · simp [getMapKeys_single, st, ha, splitT] at h
      cases hd : Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) with
      | error e => rw [hd] at h; cases h
      | ok x =>
        rw [hd] at h
        simp only [Lynx.Except.ok_bind, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at h
        have e := list_inj (show Term.list [] = Term.list rs from h.1)
        subst e; simp
    · simp [getMapKeys_single, st, ha, splitT, Erlang.sets.«to_list/1», Erlang.maps.«keys/1»] at h
      cases hd : Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) with
      | error e => rw [hd] at h; cases h
      | ok x =>
        rw [hd] at h
        simp only [Lynx.Except.ok_bind, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at h
        have e := list_inj h.1
        subst e
        refine List.Pairwise.map _ (fun a b ne eq => ne ?_) (mapEntries_distinct S)
        rw [eq]; exact Lynx.Term.compareExact_self _

end

section
variable {t : Term} {n : Nat}

/-- The maps of an update at a key with `:keep` or `:reject`, on the maps of a type. -/
def KeepX (t : Term) (n : Nat) (X : List (Term × Term)) (v : Term) (keep : Bool) (a : String)
    (w : MW (level t n).V) : Prop :=
  (PutAt (level t n).den v a w ∧ ∃ x, MT t n X (setK a (some x) w)) ∨
    (keep = Bool.true ∧ w (.atom a) = none ∧ MT t n X w)

/-- `map_update_static/5` for `:keep` and `:reject` of a static value at a list of atoms, on a map field. -/
theorem keep_atoms_static {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b)
    (fb : MField (level t n).E b) {v : Term} (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x) (keep : Bool)
    (A : List String) (lk : String → Bool) (hlk : ∀ a, lk a = Bool.true ↔ ∃ w, MT t n X w ∧ w (.atom a) = none)
    (k : Nat) (hk : (level t n).K + 4 ≤ k) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 6)) (.map X)
        (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true")
        (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, ¬MT t n X w) ∨
        (∃ w, MT t n X w) ∧ ∃ (T Y : Term) (f : Bool), res = .tuple #[T, Y,
          Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f] ∧
        ((Y = .map [] ∧ ∀ w, ¬∃ a ∈ A, KeepX t n X v keep a w) ∨
          ∃ r, Y = .map [(.atom "map", r)] ∧ MField (level t n).E r ∧
            ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔ ∃ a ∈ A, KeepX t n X v keep a w) ∧
        (level t n).E T ∧ (∀ x, (level t n).den T x ↔ ∃ a ∈ A, ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧
        (f = Bool.true ↔ ∃ a ∈ A, ¬∃ w, MT t n X w ∧ w (.atom a) = none)) := by
  have ef := (level t n).ef
  have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
  have conv : ∀ (lines : List Term), (∀ w, denMF (level t n).E (level t n).den b w = Bool.true ↔
      ∃ L ∈ lines, InMLine (level t n).den L w) → lines ≠ [] → (∀ L ∈ lines, MLine (level t n).E L ∧ ∃ w, InMLine (level t n).den L w) →
      ∃ (T Y : Term) (f : Bool), Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (k + 6)) b (Term.list lines)
        (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true")
        (.atom "true") = .ok (.tuple #[T, Y,
          Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a]), boolAtom f]) ∧
        ((Y = .map [] ∧ ∀ w, ¬∃ a ∈ A, KeepX t n X v keep a w) ∨
          ∃ r, Y = .map [(.atom "map", r)] ∧ MField (level t n).E r ∧
            ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔ ∃ a ∈ A, KeepX t n X v keep a w) ∧
        (level t n).E T ∧ (∀ x, (level t n).den T x ↔ ∃ a ∈ A, ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧
        (f = Bool.true ↔ ∃ a ∈ A, ¬∃ w, MT t n X w ∧ w (.atom a) = none) := by
    intro lines sl hne hl
    obtain ⟨T, Y, f, run, hY, hT, sT, sf⟩ := keep_atoms_lines ef (n := k) hk hv vne keep lines hl hne sl A lk
      (fun a => by rw [hlk]; simp only [mt])
    have kx : ∀ a w, KeepB (level t n).E (level t n).den v keep b a w ↔ KeepX t n X v keep a w := fun a w => by
      simp only [KeepB, KeepX, mt]
    refine ⟨T, Y, f, run, ?_, hT, fun x => by rw [sT]; simp only [mt], by rw [sf]; simp only [mt]⟩
    rcases hY with ⟨e, h⟩ | ⟨r, e, fr, sr⟩
    · exact Or.inl ⟨e, fun w ⟨a, ma, h'⟩ => h w ⟨a, ma, (kx a w).mpr h'⟩⟩
    · exact Or.inr ⟨r, e, fr, fun w => by rw [sr]; simp only [kx]⟩
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨kk, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF (level t n).E (level t n).den (.tuple #[.integer kk, tag, fieldsTerm l]) w = Bool.true ↔
        MSem (level t n).den tag l w := fun w => denMF_leaf ef sl g w
    obtain ⟨e, ri⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have ri : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (k + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := ri (k + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem (level t n).den tag l w := Classical.byContradiction fun none => by
        have := ri.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := k + 6) (by omega) rfl g sl
          (negs := []) (by simp) fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine (level t n).E L ∧
          ∃ w, InMLine (level t n).den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      have inB : ∀ w, denMF (level t n).E (level t n).den (.tuple #[.integer kk, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine (level t n).den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      obtain ⟨T, Y, f, run, rest⟩ := conv _ inB (by simp) hl
      refine ⟨_, ?_, Or.inr ⟨⟨w₀, (mt w₀).mpr ((sem w₀).mpr h₀)⟩, T, Y, f, rfl, rest⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, Term.list]
      simpa [Term.list] using run
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w hw => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom]
      · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := k + 6) (by omega) rfl g sl
          (negs := []) (by simp) ri w ((sem w).mp ((mt w).mp hw))
        simp at mN
  · have wb : Bdd (MLit (level t n).E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := (level t n).den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := k + 6) (by omega) wb
    have inB : ∀ w, denMF (level t n).E (level t n).den b w = Bool.true ↔ ∃ L ∈ lines, InMLine (level t n).den L w :=
      fun w => by rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w hw => by simpa using (inB w).mp ((mt w).mp hw)⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, Term.list]
      · simp [getMapKeys_single, hb, rl, Term.list]
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, Term.list]
    | cons L rest =>
      obtain ⟨T, Y, f, run, rest'⟩ := conv _ inB (by simp) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨⟨w₀, (mt w₀).mpr ((inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩)⟩, T, Y, f, rfl, rest'⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using run
      · simpa [getMapKeys_single, hb, rl, Term.list] using run
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using run


/-- `map_update/5` for `:keep` and `:reject` of a static value at a list of atoms, asking for the old values, in
static types of the next level. -/
theorem update_keep_atoms {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {A : List String}
    {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)))
    {v : Term} (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) (keep : Bool)
    (hm : (level t n).K + 26 ≤ m) (lk : String → Bool)
    (hlk : ∀ a, lk a = Bool.true ↔ ∃ w, MT t n X w ∧ w (.atom a) = none) :
    ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (modeT keep) (.atom "true") = .ok r ∧
      ((r = .atom "badmap" ∧ ¬MOnly t n X) ∨ MOnly t n X ∧ ∃ (T : Term) (Y : List (Term × Term)) (f : Bool),
        ((f = Bool.true ∧ r = .tuple #[T, .map Y,
            Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a])]) ∨
          (f = Bool.false ∧ r = .tuple #[.atom "error",
            Term.list ((A.filter lk).reverse.map fun a => Term.tuple #[.atom "badkey", .atom a])])) ∧
        DE (level t n).E (.map Y) ∧ (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
        (∀ w, MT t n Y w ↔ ∃ a ∈ A, KeepX t n X v keep a w) ∧
        (level t n).E T ∧ (∀ x, (level t n).den T x ↔ ∃ a ∈ A, ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧
        (f = Bool.true ↔ ∃ a ∈ A, ¬∃ w, MT t n X w ∧ w (.atom a) = none)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D (k + 6)) (.map X) key v (modeT keep) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
        (splitT (A.map Term.atom) (.atom "nil") (([] : List String).map Term.atom)) (keepOp v keep) (.atom "true") := by
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
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
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
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨⟨w₀, hw₀⟩, T, Y, f, rfl, hY, hT, sT, sf⟩⟩ :=
        keep_atoms_static hb fb hv vne keep A lk hlk k (by omega)
      all_goals simp only [List.map_nil] at run
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => emp _ h.2.choose_spec⟩⟩
        simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
      have mOnly := only.mpr ⟨restE, w₀, (mt w₀).mp hw₀⟩
      obtain ⟨Yl, rfl, dY, oY, sY⟩ : ∃ Yl : List (Term × Term), Y = .map Yl ∧ DE (level t n).E (.map Yl) ∧
          (∀ q : PN t n, denD (.map Yl) q → q.1.1 = "map") ∧ ∀ w, MT t n Yl w ↔ ∃ a ∈ A, KeepX t n X v keep a w := by
        rcases hY with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
        · refine ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_⟩
          · rw [denD_map] at hq; simp [mapLookup, dn_none] at hq
          · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
            exact emp w
        · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_⟩
          · rw [denD_map] at hq
            by_cases e : q.1.1 = "map"
            · exact e
            · simp [mapLookup, e, dn_none] at hq
          · rw [← sr]; simp [MT, mapLookup]
      cases f
      · refine ⟨_, ?_, Or.inr ⟨mOnly, T, Yl, Bool.false, Or.inr ⟨rfl, rfl⟩, dY, oY, sY, hT, sT, sf⟩⟩
        simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
      · refine ⟨_, ?_, Or.inr ⟨mOnly, T, Yl, Bool.true, Or.inl ⟨rfl, rfl⟩, dY, oY, sY, hT, sT, sf⟩⟩
        simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

end

section
variable {t : Term} {n : Nat}

theorem atoms_compare_eq : ∀ (A B : List String),
    Term.compare (Term.fuel (Term.list (A.map Term.atom)) (Term.list (B.map Term.atom))) (Term.list (A.map Term.atom))
      (Term.list (B.map Term.atom)) = .eq → A = B
  | [], [] => fun _ => rfl
  | [], b :: B => fun h => by rw [Lynx.Term.compare_step] at h; simp [Term.list, Lynx.Term.Compare.compareStep] at h
  | a :: A, [] => fun h => by rw [Lynx.Term.compare_step] at h; simp [Term.list, Lynx.Term.Compare.compareStep] at h
  | a :: A, b :: B => fun h => by
    rw [Lynx.Term.compare_step] at h
    simp [Term.list, Lynx.Term.Compare.compareStep] at h
    rw [h.1, atoms_compare_eq A B h.2]

theorem member_true {x : Term} : ∀ {ys : List Term}, x ∈ ys → Erlang.lists.«member/2» x (Term.list ys) = .ok Term.true
  | y :: ys, h => by
    rw [Erlang.lists.«member/2».eq_def]
    simp only
    by_cases e : Term.compareExact (Term.fuel x y) x y = .eq
    · simp [e]
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd (Lynx.Term.compareExact_self _) e
      · simp [e, member_true h]

theorem all_in_true {xs ys : List Term} (h : ∀ x ∈ xs, x ∈ ys) :
    Elixir.STTDescrProofsTest.«all_in?/2» (Term.list xs) (Term.list ys) = .ok (.atom "true") := by
  induction xs with
  | nil => simp [Elixir.STTDescrProofsTest.«all_in?/2»]
  | cons x xs ih =>
    rw [Elixir.STTDescrProofsTest.«all_in?/2».eq_def]
    simp [member_true (h x List.mem_cons_self), Term.true] at ih ⊢
    exact ih fun y my => h y (List.mem_cons_of_mem _ my)

/-- Permutations are `permutation?/2`. -/
theorem permutation_true {xs ys : List Term} (h : xs.Perm ys) :
    Elixir.STTDescrProofsTest.«permutation?/2» (Term.list xs) (Term.list ys) = .ok (.atom "true") := by
  simp [Elixir.STTDescrProofsTest.«permutation?/2», length_list, h.length_eq, Erlang.erlang.«==/2»,
    all_in_true fun x mx => h.mem_iff.mp mx, all_in_true fun x mx => h.mem_iff.mpr mx, Lynx.Except.andAlso]

/-- The open map type with a required key. -/
theorem has_key_run (a : String) (m : Nat) :
    ∃ H, Elixir.STTDescrProofsTest.«has_key/1» (D (m + 1)) (.atom a) = .ok (.map H) ∧ DE (level t n).E (.map H) ∧
      (∀ q : PN t n, denD (.map H) q → q.1.1 = "map") ∧ ∀ w, MT t n H w ↔ ∃ x, w (.atom a) = some x := by
  have hterm : (level t n).E (.atom "term") := (level t n).ef.term
  obtain ⟨k, rom, key⟩ := open_map_run a ((level t n).ef.static hterm) m
  refine ⟨_, by simp [Elixir.STTDescrProofsTest.«has_key/1», Elixir.Module.Types.Descr.«term/0», rom],
    mfused_de (mleaf_field (Or.inl rfl) (fieldsV_req hterm) key), fun q hq => ?_, fun w => ?_⟩
  · rw [denD_map] at hq
    by_cases e : q.1.1 = "map"
    · exact e
    · simp [mapLookup, e, dn_none] at hq
  · rw [mt_open_at hterm a k]; simp [(level t n).ef.den_term]

theorem mt_of_pt (q : PN t n) (hq : q.1.1 = "map") :
    ∃ w, (∀ Z' : List (Term × Term), denD (.map Z') q ↔ MT t n Z' w) := pt_map q hq

/-- `lacking/2` lists the atoms some map of a type lacks. -/
theorem lacking_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (only : MOnly t n X) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) (lk : String → Bool)
    (hlk : ∀ a, lk a = Bool.true ↔ ∃ w, MT t n X w ∧ w (.atom a) = none) (A : List String) :
    Elixir.STTDescrProofsTest.«lacking/2» (D (m + 1)) (.map X) (Term.list (A.map Term.atom)) =
      .ok (Term.list ((A.filter lk).map fun a => Term.tuple #[.atom "badkey", .atom a])) := by
  induction A with
  | nil => simp [Elixir.STTDescrProofsTest.«lacking/2», Term.list, pure, Except.pure]
  | cons a A ih =>
    obtain ⟨H, rH, dH, oH, sH⟩ := has_key_run (t := t) (n := n) a m
    have sub := next_sub hX dH (m := m + 1) (by omega)
    have e : SubN t n (.map X) (.map H) ↔ lk a = Bool.false := by
      constructor
      · intro hs
        cases h : lk a
        · rfl
        · obtain ⟨w, hw, wa⟩ := (hlk a).mp h
          obtain ⟨x, hx⟩ := (sH w).mp ((denD_mpt w).mp (hs _ ((denD_mpt w).mpr hw)))
          rw [wa] at hx; cases hx
      · intro h q hq
        obtain ⟨w, hw⟩ := pt_map q (only.1 q hq)
        rw [hw] at hq ⊢
        rw [sH]
        cases wa : w (.atom a) with
        | some x => exact ⟨x, rfl⟩
        | none => have := (hlk a).mpr ⟨w, hq, wa⟩; rw [h] at this; cases this
    rw [Elixir.STTDescrProofsTest.«lacking/2».eq_def]
    simp only [Term.list, List.map] at ih ⊢
    cases h : lk a
    · rw [bp_true.mpr (e.mpr h)] at sub
      simp [rH, sub, ih, h, boolAtom]
    · rw [bp_false.mpr fun hs => by rw [e.mp hs] at h; cases h] at sub
      simp [rH, sub, ih, h, boolAtom, Term.list, pure, Except.pure]

/-- `holding/1` is the type of the maps holding every atom. -/
theorem holding_run {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ A : List String, ∃ H, Elixir.STTDescrProofsTest.«holding/1» (D (m + 1)) (Term.list (A.map Term.atom)) =
      .ok (.map H) ∧ DE (level t n).E (.map H) ∧ (∀ q : PN t n, denD (.map H) q → q.1.1 = "map") ∧
      ∀ w, MT t n H w ↔ ∀ a ∈ A, ∃ x, w (.atom a) = some x
  | [] => ⟨topM, by simp [Elixir.STTDescrProofsTest.«holding/1», Term.list, Elixir.Module.Types.Descr.«open_map/0»],
      mapTop_de, fun q hq => (mapTop_den q).mp hq, fun w => by simp [mt_top w]⟩
  | a :: A => by
    obtain ⟨H', rH', dH', oH', sH'⟩ := holding_run hm A
    obtain ⟨K₁, rK, dK, oK, sK⟩ := has_key_run (t := t) (n := n) a m
    obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).inter dK dH'
    have oc : ∀ q : PN t n, denD c q → q.1.1 = "map" := fun q hq => oK q ((sc q).mp hq).1
    obtain ⟨Z, rfl⟩ := map_only_shape hc oc
    refine ⟨Z, ?_, hc, oc, fun w => ?_⟩
    · rw [Elixir.STTDescrProofsTest.«holding/1».eq_def]
      simp only [Term.list, List.map] at rH' ⊢
      simp [rK, rH', rc (m + 1) (by omega)]
    · rw [← denD_mpt, sc, denD_mpt, denD_mpt, sK, sH']
      simp

/-- `updates/3` unites the puts at each atom into the maps holding it. -/
theorem updates_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (only : MOnly t n X) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∀ A : List String, ∃ U, Elixir.STTDescrProofsTest.«updates/3» (D (m + 1)) (.map X) (Term.list (A.map Term.atom)) v =
      .ok (.map U) ∧ DE (level t n).E (.map U) ∧ (∀ q : PN t n, denD (.map U) q → q.1.1 = "map") ∧
      ∀ w, MT t n U w ↔ ∃ a ∈ A, PutAt (level t n).den v a w ∧ ∃ x, MT t n X (setK a (some x) w)
  | [] => ⟨[], by simp [Elixir.STTDescrProofsTest.«updates/3», Term.list, Elixir.Module.Types.Descr.«none/0»],
      Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => by rw [denD_map] at hq; simp [mapLookup, dn_none] at hq,
      fun w => by simp [MT, mapLookup]⟩
  | a :: A => by
    obtain ⟨U', rU', dU', oU', sU'⟩ := updates_run hX only hv sv hm A
    obtain ⟨H, rH, dH, oH, sH⟩ := has_key_run (t := t) (n := n) a m
    obtain ⟨c, hc, rc, sc⟩ := (ef_next t n).opt_inter [] hX dH (m := m + 1) (by omega)
    have oc : ∀ q : PN t n, denD c q → q.1.1 = "map" := fun q hq => only.1 q ((sc q).mp hq).1
    obtain ⟨C, rfl⟩ := map_only_shape hc oc
    have sC : ∀ u, MT t n C u ↔ MT t n X u ∧ ∃ x, u (.atom a) = some x := fun u => by
      rw [← denD_mpt, sc, denD_mpt, denD_mpt, sH]
    have emp := next_empty hc (m := m + 1) (by omega)
    rw [Elixir.STTDescrProofsTest.«updates/3».eq_def]
    simp only [Term.list, List.map] at rU' ⊢
    by_cases ne : ∀ q : PN t n, ¬denD (.map C) q
    · rw [bp_true.mpr ne] at emp
      refine ⟨U', ?_, dU', oU', fun w => ?_⟩
      · simp [rH, Elixir.Module.Types.Descr.«opt_intersection/2», rc, emp, boolAtom, rU']
      · rw [sU']
        simp only [List.mem_cons]
        constructor
        · rintro ⟨a', ma, h⟩; exact ⟨a', Or.inr ma, h⟩
        · rintro ⟨a', rfl | ma, h⟩
          · obtain ⟨-, x, hx⟩ := h
            exact absurd ((denD_mpt _).mpr ((sC _).mpr ⟨hx, x, by simp [setK]⟩)) (ne _)
          · exact ⟨a', ma, h⟩
    · rw [bp_false.mpr ne] at emp
      obtain ⟨q, hq⟩ : ∃ q : PN t n, denD (.map C) q := Classical.byContradiction fun h => ne fun q hq => h ⟨q, hq⟩
      obtain ⟨w₀, hw₀⟩ := pt_map q (oc q hq)
      have onlyC : MOnly t n C := ⟨oc, w₀, (hw₀ C).mp hq⟩
      obtain ⟨res, run, ⟨-, no⟩ | ⟨Ya, rfl, -, dYa, oYa, sYa⟩⟩ := put_map hc a hv sv (m := m + 1) (by omega)
      · exact absurd onlyC no
      obtain ⟨u, hu, ru, su, -⟩ := (ef_next t n).union dYa dU'
      have ou : ∀ q : PN t n, denD u q → q.1.1 = "map" := fun q hq => by
        rcases (su q).mp hq with h | h
        · exact oYa q h
        · exact oU' q h
      obtain ⟨Uz, rfl⟩ := map_only_shape hu ou
      refine ⟨Uz, ?_, hu, ou, fun w => ?_⟩
      · simp [rH, Elixir.Module.Types.Descr.«opt_intersection/2», rc, emp, boolAtom, run, Erlang.erlang.«element/2», rU',
          ru (m + 1) (by omega)]
      · rw [← denD_mpt, su, denD_mpt, denD_mpt, sYa, sU']
        simp only [List.mem_cons]
        have e : ∀ o, MT t n C (setK a o w) ↔ ∃ x, o = some x ∧ MT t n X (setK a (some x) w) := fun o => by
          rw [sC]
          cases o with
          | none => simp [setK]
          | some x => simp [setK]
        simp only [e]
        constructor
        · rintro (⟨p, o, x, rfl, h⟩ | ⟨a', ma, h⟩)
          · exact ⟨a, Or.inl rfl, p, x, h⟩
          · exact ⟨a', Or.inr ma, h⟩
        · rintro ⟨a', rfl | ma, p, x, h⟩
          · exact Or.inl ⟨p, some x, x, rfl, h⟩
          · exact Or.inr ⟨a', ma, p, x, h⟩

/-- `updated/4` gives the maps of the updates at the atoms, and with `:keep` the maps lacking some atom. -/
theorem updated_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (only : MOnly t n X) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) (A : List String) (keep : Bool) :
    ∃ U, Elixir.STTDescrProofsTest.«updated/4» (D (m + 1)) (.map X) (Term.list (A.map Term.atom)) v (modeT keep) =
      .ok (.map U) ∧ DE (level t n).E (.map U) ∧ (∀ q : PN t n, denD (.map U) q → q.1.1 = "map") ∧
      ∀ w, MT t n U w ↔ ∃ a ∈ A, KeepX t n X v keep a w := by
  obtain ⟨U, rU, dU, oU, sU⟩ := updates_run hX only hv sv hm A
  cases keep
  · refine ⟨U, by simpa [Elixir.STTDescrProofsTest.«updated/4», modeT] using rU, dU, oU, fun w => ?_⟩
    rw [sU]; simp [KeepX]
  · obtain ⟨H, rH, dH, oH, sH⟩ := holding_run (t := t) (n := n) (m := m) (by omega) A
    obtain ⟨c, hc, rc, sc⟩ := (ef_next t n).opt_diff [] hX dH (m := m + 1) (by omega)
    obtain ⟨u, hu, ru, su, -⟩ := (ef_next t n).union dU hc
    have ou : ∀ q : PN t n, denD u q → q.1.1 = "map" := fun q hq => by
      rcases (su q).mp hq with h | h
      · exact oU q h
      · exact only.1 q ((sc q).mp h).1
    obtain ⟨Uz, rfl⟩ := map_only_shape hu ou
    refine ⟨Uz, ?_, hu, ou, fun w => ?_⟩
    · simp [Elixir.STTDescrProofsTest.«updated/4», modeT, rU, rH, Elixir.Module.Types.Descr.«opt_difference/2», rc,
        ru (m + 1) (by omega)]
    · rw [← denD_mpt, su, denD_mpt, sU, sc, denD_mpt, denD_mpt, sH]
      simp only [KeepX, true_and]
      constructor
      · rintro (⟨a, ma, h⟩ | ⟨hx, hn⟩)
        · exact ⟨a, ma, Or.inl h⟩
        · obtain ⟨a, ma, ha⟩ : ∃ a ∈ A, w (.atom a) = none := Classical.byContradiction fun hc => hn fun a ma => by
            cases e : w (.atom a) with
            | none => exact absurd ⟨a, ma, e⟩ hc
            | some x => exact ⟨x, rfl⟩
          exact ⟨a, ma, Or.inr ⟨ha, hx⟩⟩
      · rintro ⟨a, ma, h | ⟨hn, hx⟩⟩
        · exact Or.inl ⟨a, ma, h⟩
        · exact Or.inr ⟨hx, fun hall => by obtain ⟨x, hx'⟩ := hall a ma; rw [hn] at hx'; cases hx'⟩

end

end Elixir.STTDescrProofsTest.Nest
