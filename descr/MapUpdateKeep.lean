module

public import Erlang.program
public import MapPutDomain

@[expose] public section

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

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Updates with a constant field: a type, whether it is optional, and what to do with absent keys. -/
abbrev cOp (nt : Term) (nopt : Bool) (md : String) : Term :=
  .tuple #[.tuple #[.atom "constant", .tuple #[nt, boolAtom nopt]], .atom md]

/-- The modes of updates. -/
def Mode (md : String) : Prop := md = "force" ∨ md = "keep" ∨ md = "reject"

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The new field of an update of a key whose old field allows `Old`: the new field where the key held a value,
and where it was absent, the new field when forcing or absence when keeping. -/
def NewF (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (Old : Option V → Prop) (o : Option V) : Prop :=
  ((∃ x, Old (some x)) ∧ ((o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x)) ∨
    (Old none ∧ ((md = "force" ∧ ((o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x)) ∨
      (md = "keep" ∧ o = none)))

theorem update_field_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {old : Term} (ho : FieldValue E old) :
    ∃ F, Elixir.Module.Types.Descr.«map_update_field/2» (D m) old (cOp nt nopt md) = .ok F ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ NewF den nt nopt md (FieldSem den old) o := by
  obtain ⟨t, opt, rfl, ht⟩ := ho
  obtain ⟨e, re, se⟩ := ef.empty1 (m := m) hm ht
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  -- The present part and the absent part.
  let pt : Term := if e then .map [] else nt
  let po : Bool := if e then Bool.false else nopt
  let at' : Term := if opt ∧ md = "force" then nt else .map []
  let ao : Bool := if opt ∧ md = "force" then nopt else if opt ∧ md = "keep" then Bool.true else Bool.false
  have hpt : E pt := by by_cases h : e = Bool.true <;> simp [pt, h, ef.none, hnt]
  have hat : E at' := by by_cases h : opt = Bool.true ∧ md = "force" <;> simp only [at', h] <;> simp [ef.none, hnt]
  obtain ⟨F, hF, rF, sF⟩ := field_opt_union_val (den := den) ef (m := m) hm (f₁ := .tuple #[pt, boolAtom po])
    (f₂ := .tuple #[at', boolAtom ao]) rfl rfl hpt hat []
  refine ⟨_, ?_, ⟨F, po || ao, rfl, hF⟩, fun o => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_field/2»
    simp only [Elixir.Module.Types.Descr.«map_update_apply_callback/3», re, Lynx.Except.ok_bind]
    rcases hmd with rfl | rfl | rfl <;> cases e <;> cases opt <;> cases nopt <;>
      simp [Lynx.Term.isMember, boolAtom, Erlang.program.«Elixir.Module.Types.Descr:-map_update_field/2-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_field/2-fun-0-/3», pt, at', po, ao] at rF ⊢ <;> exact rF
  · have ne : (∃ x, FieldSem den (.tuple #[t, boolAtom opt]) (some x)) ↔ e = Bool.false := by
      simp only [fieldSem_mk, reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
      constructor
      · rintro ⟨x, hx⟩; cases e; rfl; exact absurd hx (se.mp rfl x)
      · intro h; subst h
        exact Classical.byContradiction fun nx => by
          have := se.mpr fun y hy => nx ⟨y, hy⟩; cases this
    have abs : FieldSem den (.tuple #[t, boolAtom opt]) none ↔ opt = Bool.true := by simp [fieldSem_mk]
    rw [sF, NewF, ne, abs]
    simp only [fieldSem_mk]
    rcases hmd with rfl | rfl | rfl <;> cases e <;> cases opt <;> cases nopt <;>
      simp [pt, po, at', ao, nn]

/-- The values an update puts at the keys of a kind: the new type, when forcing or when some line's tag gives the
kind a value. -/
def NewDom (den : Term → V → Prop) (lines : List Term) (nt : Term) (md : String) (kind : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ ∃ L ∈ lines, ∃ y, LineTag den L kind y)

/-- What the tag of the box allows at the keys of a kind, for any constant update. -/
def BoxTagG (den : Term → V → Prop) (lines : List Term) (nt : Term) (md : String) (Ds : List String) (kind : String)
    (x : V) : Prop :=
  (∃ L ∈ lines, LineTag den L kind x) ∨ (kind ∈ Ds ∧ NewDom den lines nt md kind x)

/-- Kinds whose update field is not empty. -/
def DomNE (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String) (kind : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ ∃ L ∈ lines, ∃ y, LineTag den L kind y) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- A domain update of `map_update_box/6`: an updated kind whose new field is not empty, the type the lines give it,
and the new type. -/
def DomUpdG (E : Term → Prop) (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (u : Term) : Prop :=
  ∃ d o t, u = .tuple #[.atom d, o, t] ∧ d ∈ Ds ∧ DomNE den lines nt nopt md d ∧ E o ∧ E t ∧
    (∀ x, den o x ↔ ∃ L ∈ lines, LineTag den L d x) ∧ ∀ x, den t x ↔ NewDom den lines nt md d x

/-- The fold of `map_update_box/6` over the kinds of keys, for any constant update: the tag, and the updated
domains. -/
theorem box_domains_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K + 3 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) {nt : Term} (hnt : E nt) (nopt : Bool) {md : String} (hmd : Mode md)
    (Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ T U, Erlang.lists.«foldl/3» (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-7-" 2
          #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md])
        (.tuple #[.atom "closed", .nil]) (Term.list (domainKinds.map Term.atom)) = .ok (.tuple #[T, Term.list U]) ∧
      LowTag E T (.atom "zzz") ∧
      (∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔ BoxTagG den lines nt md Ds kind x) ∧
      (∀ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ E t) ∧
      ((∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔ ∃ d ∈ Ds, ∃ x, NewDom den lines nt md d x) ∧
      (U ≠ [] ↔ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ∧ (∀ u ∈ U, DomUpdG E den lines nt nopt md Ds u) ∧
      (∀ d ∈ Ds, DomNE den lines nt nopt md d → ∃ u ∈ U, ∃ o t, u = .tuple #[.atom d, o, t]) := by
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  let R : List Term → Term → Prop := fun pre a => ∃ T U, a = .tuple #[T, Term.list U] ∧
    (∀ d', (∀ p ∈ pre, Term.compare (Term.fuel p d') p d' = .lt) → LowTag E T d') ∧
    (∀ kind x, den (tagType T kind) x ↔ .atom kind ∈ pre ∧ BoxTagG den lines nt md Ds kind x) ∧
    (∀ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ E t) ∧
    ((∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔
      ∃ d ∈ Ds, .atom d ∈ pre ∧ ∃ x, NewDom den lines nt md d x) ∧
    (U ≠ [] ↔ ∃ d ∈ Ds, .atom d ∈ pre ∧ DomNE den lines nt nopt md d) ∧
    (∀ u ∈ U, DomUpdG E den lines nt nopt md Ds u) ∧
    (∀ d ∈ Ds, .atom d ∈ pre → DomNE den lines nt nopt md d → ∃ u ∈ U, ∃ o t, u = .tuple #[.atom d, o, t])
  obtain ⟨r, ⟨T, U, rfl, low, sem, du, pu, ne, dg, cv⟩, run⟩ := foldl_prefix_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_box/6-fun-7-" #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md] R
    (domainKinds.map Term.atom)
    (fun pre x rest a e ⟨T, U, ha, low, sem, du, pu, ne, dg, cv⟩ => by
      subst ha
      have mx : x ∈ domainKinds.map Term.atom := by rw [← e]; simp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mx
      have before : ∀ p ∈ pre, Term.compare (Term.fuel p (.atom d)) p (.atom d) = .lt := by
        have := kinds_sorted; rw [← e, List.pairwise_append] at this
        exact fun p mp => this.2.2 p mp _ List.mem_cons_self
      have notPre : Term.atom d ∉ pre := fun m => by
        have := before _ m
        rw [Lynx.Term.compare_self] at this
        cases this
      obtain ⟨old, rold, hold, sold⟩ := get_domain1 ef (n := n) (by omega) lines hl d
      have pureE : ∀ a, (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-7-" 2
          #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.atom d, a] =
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5» (D n) (Term.list lines) (Term.list (Ds.map Term.atom))
            (cOp nt nopt md) (.atom d) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-7-/2».pure]
      -- The kind's new type and the updates, then the tag.
      have finish : ∀ type U', E type → (∀ x, den type x ↔ den old x ∨ (d ∈ Ds ∧ NewDom den lines nt md d x)) →
          (∀ u ∈ U', ∃ d o t, u = .tuple #[d, o, t] ∧ E t) →
          ((∃ u ∈ U', ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔
            (∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ∨ (d ∈ Ds ∧ ∃ x, NewDom den lines nt md d x)) →
          (U' ≠ [] ↔ U ≠ [] ∨ (d ∈ Ds ∧ DomNE den lines nt nopt md d)) →
          (∀ u ∈ U', DomUpdG E den lines nt nopt md Ds u) →
          (∀ d' ∈ Ds, .atom d' ∈ pre ++ [.atom d] → DomNE den lines nt nopt md d' →
            ∃ u ∈ U', ∃ o t, u = .tuple #[.atom d', o, t]) →
          ∃ T', Elixir.Module.Types.Descr.«map_replace_domain/3» (D n) T (.atom d) type = .ok T' ∧
            R (pre ++ [.atom d]) (.tuple #[T', Term.list U']) := fun type U' hty stype du' pu' ne' dg' cv' => by
        obtain ⟨T', rT, low', sT'⟩ := replace_domain ef hd (low _ before) hty n
        refine ⟨T', rT, T', U', rfl, fun d' h => low' d' (h _ (by simp)), fun kind x => ?_, du', ?_, ?_, dg', cv'⟩
        · rw [sT']
          by_cases k : kind = d
          · subst k
            rw [ite_eq_left rfl, stype, sold]
            simp only [BoxTagG, List.mem_append, List.mem_singleton, or_true, true_and]
          · rw [ite_eq_right k, sem]
            simp [k]
        · rw [pu', pu]
          constructor
          · rintro (⟨d', md', hm, hx⟩ | ⟨md', hx⟩)
            · exact ⟨d', md', List.mem_append_left _ hm, hx⟩
            · exact ⟨d, md', by simp, hx⟩
          · rintro ⟨d', md', hm, hx⟩
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl ⟨d', md', hm, hx⟩
            · simp at hm; subst hm; exact Or.inr ⟨md', hx⟩
        · rw [ne', ne]
          constructor
          · rintro (⟨d', md', hm, hx⟩ | ⟨md', hx⟩)
            · exact ⟨d', md', List.mem_append_left _ hm, hx⟩
            · exact ⟨d, md', by simp, hx⟩
          · rintro ⟨d', md', hm, hx⟩
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl ⟨d', md', hm, hx⟩
            · simp at hm; subst hm; exact Or.inr ⟨md', hx⟩
      have mem := member_atoms d Ds
      by_cases up : d ∈ Ds
      · simp only [up, ↓reduceIte] at mem
        obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef (m := n) (by omega) hnt nopt hmd
          (old := .tuple #[old, .atom "true"]) ⟨old, Bool.true, rfl, hold⟩
        obtain ⟨ft, fo, rfl, hft⟩ := hF
        have hn : FieldSem den (.tuple #[old, .atom "true"]) none := by
          rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
        have sOld : (∃ x, FieldSem den (.tuple #[old, .atom "true"]) (some x)) ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
          rw [show (Term.atom "true") = boolAtom Bool.true from rfl]
          simp only [fieldSem_mk, reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
          exact ⟨fun ⟨y, hy⟩ => let ⟨L, mL, h⟩ := (sold y).mp hy; ⟨L, mL, y, h⟩,
            fun ⟨L, mL, y, h⟩ => ⟨y, (sold y).mpr ⟨L, mL, h⟩⟩⟩
        have sft : ∀ x, den ft x ↔ NewDom den lines nt md d x := fun x => by
          have := sF (some x)
          rw [fieldSem_mk] at this
          simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
          rw [this, NewF, NewDom, sOld]
          simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
          constructor
          · rintro (⟨ho, hx⟩ | ⟨-, (⟨rfl, hx⟩ | ⟨-, h⟩)⟩)
            · exact ⟨hx, Or.inr ho⟩
            · exact ⟨hx, Or.inl rfl⟩
            · cases h
          · rintro ⟨hx, rfl | ho⟩
            · exact Or.inr ⟨hn, Or.inl ⟨rfl, hx⟩⟩
            · exact Or.inl ⟨ho, hx⟩
        obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef (m := n) (by omega) ⟨ft, fo, rfl, hft⟩
        have neF : b = Bool.false ↔ DomNE den lines nt nopt md d := by
          rw [← Bool.not_eq_true, sb, DomNE]
          simp only [Classical.not_forall, Classical.not_not]
          constructor
          · rintro ⟨o, ho⟩
            rcases (sF o).mp ho with ⟨hold', hv'⟩ | ⟨-, (⟨rfl, hv'⟩ | ⟨rfl, -⟩)⟩
            · rcases hv' with ⟨-, h⟩ | ⟨x, -, hx⟩
              · exact Or.inr ⟨Or.inr (sOld.mp hold'), Or.inl h⟩
              · exact Or.inr ⟨Or.inr (sOld.mp hold'), Or.inr ⟨x, hx⟩⟩
            · rcases hv' with ⟨-, h⟩ | ⟨x, -, hx⟩
              · exact Or.inr ⟨Or.inl rfl, Or.inl h⟩
              · exact Or.inr ⟨Or.inl rfl, Or.inr ⟨x, hx⟩⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hf, hv'⟩)
            · exact ⟨none, (sF none).mpr (Or.inr ⟨hn, Or.inr ⟨rfl, rfl⟩⟩)⟩
            · rcases hv' with h | ⟨x, hx⟩
              · rcases hf with rfl | ho
                · exact ⟨none, (sF none).mpr (Or.inr ⟨hn, Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩⟩)⟩
                · exact ⟨none, (sF none).mpr (Or.inl ⟨sOld.mpr ho, Or.inl ⟨rfl, h⟩⟩)⟩
              · rcases hf with rfl | ho
                · exact ⟨some x, (sF _).mpr (Or.inr ⟨hn, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx⟩⟩⟩)⟩
                · exact ⟨some x, (sF _).mpr (Or.inl ⟨sOld.mpr ho, Or.inr ⟨x, rfl, hx⟩⟩)⟩
        cases b
        · obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hold hft (m := n) (by omega)
          obtain ⟨T', rT, hR⟩ := finish c (.tuple #[.atom d, old, ft] :: U) hc
            (fun x => by rw [sc, sft]; simp [up]) (fun u mu => by
              rcases List.mem_cons.mp mu with rfl | mu
              · exact ⟨_, _, _, rfl, hft⟩
              · exact du u mu)
            (by
              constructor
              · rintro ⟨u, mu, d', o, t, rfl, x, hx⟩
                rcases List.mem_cons.mp mu with e | mu
                · obtain ⟨-, -, rfl⟩ := tuple3_inj e; exact Or.inr ⟨up, x, (sft x).mp hx⟩
                · exact Or.inl ⟨_, mu, d', o, t, rfl, x, hx⟩
              · rintro (⟨u, mu, h⟩ | ⟨-, x, hx⟩)
                · exact ⟨u, List.mem_cons_of_mem _ mu, h⟩
                · exact ⟨_, List.mem_cons_self, _, _, _, rfl, x, (sft x).mpr hx⟩)
            (by simp [up, neF.mp rfl])
            (fun u mu => by
              rcases List.mem_cons.mp mu with rfl | mu
              · exact ⟨d, old, ft, rfl, up, neF.mp rfl, hold, hft, sold, sft⟩
              · exact dg u mu)
            (fun d' md' hp hne => by
              rcases List.mem_append.mp hp with hp | hp
              · obtain ⟨u, mu, h⟩ := cv d' md' hp hne; exact ⟨u, List.mem_cons_of_mem _ mu, h⟩
              · simp at hp; subst hp; exact ⟨_, List.mem_cons_self, _, _, rfl⟩)
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, mem, Term.true,
            rF, Elixir.Module.Types.Descr.«opt_union/2», rc]
          rw [rb]
          simp [boolAtom, rT]
        · have nF : ¬DomNE den lines nt nopt md d := fun h => by have := neF.mpr h; cases this
          have nNew : ∀ x, ¬NewDom den lines nt md d x := fun x hx => by
            have := (sb.mp rfl) (some x)
            exact this ((sF _).mpr (by
              rcases hx.2 with rfl | ho
              · exact Or.inr ⟨hn, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx.1⟩⟩⟩
              · exact Or.inl ⟨sOld.mpr ho, Or.inr ⟨x, rfl, hx.1⟩⟩))
          obtain ⟨T', rT, hR⟩ := finish old U hold
            (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd hx (nNew x)⟩) du
            ⟨Or.inl, fun h => h.elim id fun ⟨_, x, hx⟩ => absurd hx (nNew x)⟩
            ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd hx nF⟩ dg
            (fun d' md' hp hne => by
              rcases List.mem_append.mp hp with hp | hp
              · exact cv d' md' hp hne
              · simp at hp; subst hp; exact absurd hne nF)
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, mem, Term.true, rF]
          rw [rb]
          simp [boolAtom, rT, Elixir.Module.Types.Descr.«-map_update_box/6-fun-6-/3»]
      · obtain ⟨T', rT, hR⟩ := finish old U hold
          (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩) du
          ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩
          ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩ dg
          (fun d' md' hp hne => by
            rcases List.mem_append.mp hp with hp | hp
            · exact cv d' md' hp hne
            · simp at hp; subst hp; exact absurd md' up)
        refine ⟨_, hR, ?_⟩
        rw [pureE]
        have nm : Erlang.lists.«member/2» (.atom d) (Term.list (Ds.map Term.atom)) = .ok (.atom "false") := by
          simpa [up, Term.false] using mem
        simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, nm, rT,
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-6-/3»,
          Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-6-/1».pure])
    _ ⟨.atom "closed", [], rfl, fun _ _ => Or.inl rfl, fun kind x => by simp [tagType, nn], fun u mu => by simp at mu,
      by simp, by simp, by simp, by simp⟩
  have allIn : ∀ d ∈ Ds, Term.atom d ∈ domainKinds.map Term.atom := fun d md => List.mem_map_of_mem (hD d md)
  refine ⟨T, U, run, low _ fun p mp => ?_, fun kind mk x => (sem kind x).trans ?_, du, pu.trans ?_, ne.trans ?_, dg,
    fun d md h => cv d md (allIn d md) h⟩
  · simp only [domainKinds, List.map, List.mem_cons, List.not_mem_nil, or_false] at mp
    rcases mp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [List.mem_map, mk]
  · exact ⟨fun ⟨d, md, _, h⟩ => ⟨d, md, h⟩, fun ⟨d, md, h⟩ => ⟨d, md, allIn d md, h⟩⟩
  · exact ⟨fun ⟨d, md, _, h⟩ => ⟨d, md, h⟩, fun ⟨d, md, h⟩ => ⟨d, md, allIn d md, h⟩⟩

/-- An updated named key, for any constant update: the old field, as the lines hold it, and the new one. -/
def KeyUpdG (E : Term → Prop) (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String)
    (s : String) (q : Term) : Prop :=
  ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldValue E old ∧ (∀ o, FieldSem den old o ↔ ∃ L ∈ lines, LongM den L s o) ∧
    FieldValue E new ∧ ∀ o, FieldSem den new o ↔ NewF den nt nopt md (FieldSem den old) o

/-- The fold of `map_update_box/6` over the named keys: their fields over the lines, and the updates of those
among the updated keys. -/
theorem box_fields_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {nt : Term} (hnt : E nt) (nopt : Bool) {md : String} (hmd : Mode md) (ks NK : List String)
    (nd : NK.Nodup) :
    ∃ P Q, Erlang.lists.«foldr/3» (D (n + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md])
        (.tuple #[.nil, .nil]) (Term.list (NK.map Term.atom)) = .ok (.tuple #[fieldsTerm P, Term.list Q]) ∧
      P.map Prod.fst = NK.map Term.atom ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) ∧
      (∀ s ∈ NK, s ∈ ks → ∃ q ∈ Q, KeyUpdG E den lines nt nopt md s q) ∧ (Q.map updKey).Nodup ∧
      ∀ q ∈ Q, updKey q ∈ NK.map Term.atom := by
  obtain ⟨r, ⟨P, Q, rfl, hP, fP, uQ, cQ, kQ, nQ⟩, run⟩ := foldr_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_box/6-fun-4-" #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md]
    (fun suf a => ∃ P Q, a = .tuple #[fieldsTerm P, Term.list Q] ∧ P.map Prod.fst = suf ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) ∧
      (∀ s, .atom s ∈ suf → s ∈ ks → ∃ q ∈ Q, KeyUpdG E den lines nt nopt md s q) ∧ (∀ q ∈ Q, updKey q ∈ suf) ∧
      (Q.map updKey).Nodup) (NK.map Term.atom)
    (fun pre x suf a e ⟨P, Q, ha, hP, fP, uQ, cQ, kQ, nQ⟩ => by
      subst ha
      have mx : x ∈ NK.map Term.atom := by rw [← e]; simp
      have xs : x ∉ suf := by
        have : (NK.map Term.atom).Nodup := List.pairwise_map.mpr (nd.imp fun h e => h (Term.atom.inj e))
        rw [← e] at this
        exact (List.nodup_cons.mp (List.nodup_append.mp this).2.1).1
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨old, rold, hold, sold⟩ := mdnf_fetch ef hn s lines hl
      have pureE : ∀ a, (D (n + 4)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md]) #[.atom s, a] =
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5» (D (n + 3)) (Term.list lines)
            (Term.list (ks.map Term.atom)) (cOp nt nopt md) (.atom s) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-4-/2».pure]
      have mem := member_atoms s ks
      by_cases sk : s ∈ ks
      · obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef (m := n + 3) (by omega) hnt nopt hmd hold
        obtain ⟨ft, fo, rfl, hft⟩ := hF
        refine ⟨_, ⟨(.atom s, old) :: P, .tuple #[.atom s, old, .tuple #[ft, boolAtom fo]] :: Q, rfl, by simp [hP],
          fun e me => ?_, fun q mq => ?_, fun s' ms' hs' => ?_, fun q mq => ?_, ?_⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp mq with rfl | mq
          · exact ⟨s, sk, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · exact uQ q mq
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact ⟨_, List.mem_cons_self, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · obtain ⟨q, mq, hq⟩ := cQ s' ms' hs'
            exact ⟨q, List.mem_cons_of_mem _ mq, hq⟩
        · rcases List.mem_cons.mp mq with rfl | mq
          · simp [updKey]
          · exact List.mem_cons_of_mem _ (kQ q mq)
        · refine List.nodup_cons.mpr ⟨fun m => ?_, nQ⟩
          obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
          obtain ⟨s', -, old', new', rfl, -⟩ := uQ q mq
          have := kQ _ mq
          simp only [updKey] at eq this
          rw [eq] at this
          exact xs this
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5», rold, mem, sk, rF, Term.true, fieldsTerm_cons]
      · refine ⟨_, ⟨(.atom s, old) :: P, Q, rfl, by simp [hP], fun e me => ?_, uQ, fun s' ms' hs' => ?_,
          fun q mq => List.mem_cons_of_mem _ (kQ q mq), nQ⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact absurd hs' sk
          · exact cQ s' ms' hs'
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5», rold, mem, sk, Term.false, fieldsTerm_cons])
    (.tuple #[.nil, .nil]) ⟨[], [], by simp [fieldsTerm, Term.list], rfl, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨P, Q, run, hP, fP, uQ, fun s ms hs => cQ s (List.mem_map_of_mem ms) hs, nQ, kQ⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem req_fields_any {l : List (Term × Term)} (hl : ∀ e ∈ l, FieldValue E e.2) (m : Nat) :
    ∃ b : Bool, Erlang.lists.«any/2» (D m) (.function false "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-1-" 1 #[])
      (fieldsTerm l) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ¬OptFields l) := by
  classical
  let res : Term → Bool := fun x => decide (∃ k t, x = .tuple #[k, .tuple #[t, .atom "false"]])
  have := any_list (D m) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-1-" #[] res
    (l.map fun e => .tuple #[e.1, e.2]) (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨t, o, he, -⟩ := hl e me
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-1-/1».pure]
      cases o <;> simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-1-/1», he, boolAtom,
        Erlang.erlang.«not/1», res])
  refine ⟨_, this, ?_⟩
  simp only [List.any_eq_true, List.mem_map, OptFields, Classical.not_forall, res, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨e, me, rfl⟩, k, t, he⟩
    simp only [Term.tuple.injEq] at he
    refine ⟨e, me, fun ⟨ty, h⟩ => ?_⟩
    have := congrArg (fun a : Array Term => a[1]?) he
    simp [h] at this
  · rintro ⟨e, me, h⟩
    obtain ⟨t, o, he, -⟩ := hl e me
    cases o
    · exact ⟨_, ⟨e, me, rfl⟩, e.1, t, by rw [he]; rfl⟩
    · exact absurd ⟨t, he⟩ h

/-- The check of `map_update_present?/3` keeping absent keys: whether no line holds the empty map. -/
theorem allNE_gen {m : Nat} (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ b : Bool, Erlang.lists.«all/2» (D (m + 3)) (.function false "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-4-" 1 #[])
      (Term.list lines) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ L ∈ lines, ¬InMLine den L wNone) := by
  · obtain ⟨b, rb, sb⟩ := all_sem (K' := 2) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-4-" #[] lines
      (m := m + 3) (by omega) (fun L => ¬InMLine den L wNone)
      (fun m x => Elixir.Module.Types.Descr.«-map_update_present?/3-fun-4-/1» (D m) x)
      (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-4-/1».pure])
      (fun L mL => by
        obtain ⟨tag, l, negs, rfl, -, sl, sn⟩ := hl L mL
        -- Literals of optional fields hold the empty map.
        have optAll : ∀ (l' : List (Term × Term)), FieldsV E l' → ∀ m, ∃ c : Bool,
            Erlang.lists.«all/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr"
              "-map_update_present?/3-fun-2-" 1 #[]) (fieldsTerm l') = .ok (boolAtom c) ∧ (c = Bool.true ↔ OptFields l') := by
          intro l' sl' m
          obtain ⟨c, rc, sc⟩ := all_sem (K' := 0) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-2-" #[]
            (l'.map fun e => .tuple #[e.1, e.2]) (m := m + 1) (by omega)
            (fun x => ∃ k ty, x = .tuple #[k, .tuple #[ty, .atom "true"]])
            (fun _ x => Elixir.Module.Types.Descr.«-map_update_present?/3-fun-2-/1» x)
            (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-2-/1».pure])
            (fun x mx => by
              obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
              obtain ⟨ty, o, he, -⟩ := (sl'.1 e me).2
              refine ⟨o, fun _ _ => by simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-2-/1», he], ?_⟩
              cases o <;> simp [he, boolAtom])
          refine ⟨c, rc, ?_⟩
          rw [sc]
          simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OptFields]
          constructor
          · intro h e me
            obtain ⟨k, ty, he⟩ := h e me
            simp only [Term.tuple.injEq] at he
            have := congrArg (fun a : Array Term => a[1]?) he
            simp at this
            exact ⟨ty, this⟩
          · intro h e me
            obtain ⟨ty, he⟩ := h e me
            exact ⟨e.1, ty, by rw [he]⟩
        classical
        refine ⟨decide (¬InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone), fun m hm1 => ?_,
          by simp⟩
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
        obtain ⟨c, rc, sc⟩ := any_sem (m := m + 2) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-3-" #[]
          (fun N => NSem den N wNone) negs (fun N mN => by
            obtain ⟨k, tag', l', rfl, -, sl'⟩ := sn N mN
            obtain ⟨c, rc, sc⟩ := optAll l' sl' m
            refine ⟨c, ?_, sc.trans ?_⟩
            · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-3-/1».pure]
              simpa [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-3-/1»] using rc
            · rw [← msem_none (den := den) (tag := tag') sl']
              exact ⟨fun h => ⟨k, tag', l', rfl, h⟩, fun ⟨k', t', l'', e, h⟩ => by
                obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
                cases e₂; rw [fieldsTerm_inj e₃]; exact h⟩)
        obtain ⟨r, rr, sr⟩ := req_fields_any (fun e me => (sl.1 e me).2) (m + 2)
        have eq : (r || c) = decide (¬InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone) := by
          rw [inMLine_iff, msem_none (den := den) (tag := tag) sl]
          cases r <;> cases c <;> simp_all
        rw [← eq]
        simp only [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-4-/1», Lynx.Except.orElse, pure_bind]
        erw [rr]
        cases r
        · simp only [boolAtom, Bool.false_eq_true, ↓reduceIte]
          erw [rc]
          cases c <;> rfl
        · rfl)
    exact ⟨b, rb, sb⟩

/-- `map_update_present?/3` for any constant update: when keeping, whether no update removes all values and no line
holds the empty map; otherwise, whether some update gives a value. -/
theorem present_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (nt : Term) (nopt : Bool) {md : String} (hmd : Mode md) (ups : List Term)
    (hu : ∀ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ E o ∧ E n) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«map_update_present?/3» (D (m + 3)) (cOp nt nopt md) (Term.list lines)
        (Term.list ups) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ (md = "keep" → (¬∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x) ∧
          ∀ L ∈ lines, ¬InMLine den L wNone) ∧ (md ≠ "keep" → ∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ ∃ x, den n x)) := by
  by_cases mk : md = "keep"
  · subst mk
    obtain ⟨a, ra, sa⟩ := any_sem (m := m + 3) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-0-" #[]
      (fun p => ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x) ups (fun p mp => by
        obtain ⟨o, n, rfl, ho, hn⟩ := hu p mp
        obtain ⟨en, ren, sen⟩ := ef.empty1 (m := m + 2) (by omega) hn
        obtain ⟨eo, reo, seo⟩ := ef.empty1 (m := m + 2) (by omega) ho
        have neo : eo = Bool.false ↔ ∃ x, den o x := by
          constructor
          · intro h; subst h
            exact Classical.byContradiction fun nx => by have := seo.mpr fun y hy => nx ⟨y, hy⟩; cases this
          · rintro ⟨x, hx⟩; cases eo; rfl; exact absurd hx (seo.mp rfl x)
        refine ⟨en && !eo, ?_, ?_⟩
        · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-0-/1».pure]
          cases en <;> cases eo <;>
            simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-0-/1», ren, reo, Lynx.Except.andAlso,
              Erlang.erlang.«not/1», boolAtom]
        · rw [Bool.and_eq_true, Bool.not_eq_true', neo, sen]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨o, n, rfl, h1, h2⟩
          · rintro ⟨o', n', e', h1, h2⟩
            obtain ⟨rfl, rfl⟩ : o' = o ∧ n' = n := by simp at e'; exact ⟨e'.1.symm, e'.2.symm⟩
            exact ⟨h1, h2⟩)
    obtain ⟨b, rb, sb⟩ := allNE_gen (den := den) (m := m) lines hl
    cases a
    · refine ⟨b, ?_, ?_⟩
      · simp [Elixir.Module.Types.Descr.«map_update_present?/3», ra, boolAtom, rb]
      · rw [sb]
        have : ¬∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x := fun h => by
          have := sa.mpr h; cases this
        simp [this]
    · refine ⟨Bool.false, ?_, ?_⟩
      · simp [Elixir.Module.Types.Descr.«map_update_present?/3», ra, boolAtom]
      · constructor
        · intro h; cases h
        · intro h; exact absurd (sa.mp rfl) (h.1 rfl).1
  · have hmd' : md = "force" ∨ md = "reject" := by
      rcases hmd with h | h | h
      · exact Or.inl h
      · exact absurd h mk
      · exact Or.inr h
    obtain ⟨b, rb, sb⟩ := present_any (den := den) ef (m := m + 2) (by omega)
      (.tuple #[.atom "constant", .tuple #[nt, boolAtom nopt]]) md hmd' (Term.list lines) ups
      (fun p mp => let ⟨o, n, e, _, hn⟩ := hu p mp; ⟨o, n, e, hn⟩)
    refine ⟨b, rb, ?_⟩
    rw [sb]
    simp [mk]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem box_filter_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {lines : List Term} {nt : Term} {nopt : Bool} {md : String} {ks : List String}
    (Q : List Term) (uQ : ∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) :
    ∃ Q', Erlang.lists.«filter/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-5-" 1 #[])
        (Term.list Q) = .ok (Term.list Q') ∧ Q'.Sublist Q ∧
      (∀ q ∈ Q, (∃ o, FieldSem den (updNew q) o) → q ∈ Q') ∧ ∀ q ∈ Q', ∃ o, FieldSem den (updNew q) o := by
  classical
  let res : Term → Bool := fun q => decide (∃ o, FieldSem den (updNew q) o)
  refine ⟨Q.filter res, filter_list _ _ _ _ res Q fun q mq => ?_, List.filter_sublist,
    fun q mq h => List.mem_filter.mpr ⟨mq, by simp [res, h]⟩, fun q mq => by
      have := (List.mem_filter.mp mq).2; simpa [res] using this⟩
  obtain ⟨s, -, old, new, rfl, -, -, hnew, -⟩ := uQ q mq
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm hnew
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-5-/1».pure]
  simp only [Elixir.Module.Types.Descr.«-map_update_box/6-fun-5-/1», rb, Lynx.Except.ok_bind]
  cases b
  · have : ∃ o, FieldSem den new o := Classical.byContradiction fun h => by
      have := sb.mpr fun o ho => h ⟨o, ho⟩; cases this
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]
  · have : ¬∃ o, FieldSem den new o := fun ⟨o, ho⟩ => sb.mp rfl o ho
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]

/-- The fold of `map_update_box/6` storing a single update, when replacing: the new field. -/
theorem box_store_rep {m : Nat} {P : List (Term × Term)} (sP : FieldsV E P) {s : String} {old new : Term}
    (fnew : FieldValue E new) :
    ∃ P2, Erlang.lists.«foldl/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-11-" 2
        #[.atom "true"]) (fieldsTerm P) (Term.list [.tuple #[.atom s, old, new]]) = .ok (fieldsTerm P2) ∧ FieldsV E P2 ∧
      mapLookup P2 (.atom s) = some new ∧ ∀ s', s' ≠ s → mapLookup P2 (.atom s') = mapLookup P (.atom s') := by
  obtain ⟨P3, rP3, sP3, -, look3⟩ := store_val s fnew sP
  refine ⟨P3, ?_, sP3, by rw [look3]; simp, fun s' ne => by rw [look3]; simp [Ne.symm ne]⟩
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-11-/2».pure,
    Elixir.Module.Types.Descr.«-map_update_box/6-fun-11-/3», Lynx.Term.isMember, rP3]


/-- The maps of the box of an update, for any constant update: at each named key its old values, unless replaced,
or the new field of the updated keys, and at other keys what the tag of the box allows. -/
def BoxSynG (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (R : String → Prop) (nt : Term)
    (nopt : Bool) (md : String) (Ds : List String) (w : MW V) : Prop :=
  (∀ s ∈ NK, (¬R s ∧ ∃ L ∈ lines, LongM den L s (w (.atom s))) ∨
      (s ∈ ks ∧ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (w (.atom s)))) ∧
  (∀ s, s ∉ NK → w (.atom s) = none ∨ ∃ x, w (.atom s) = some x ∧ BoxTagG den lines nt md Ds "atom" x) ∧
  ∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧ BoxTagG den lines nt md Ds (domKind k) x

/-- Named keys whose update gives some field. -/
def KeyNE (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool) (md : String)
    (s : String) : Prop :=
  s ∈ NK ∧ s ∈ ks ∧ ∃ o, NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) o

/-- Whether an update has old values or new values at a named key or a kind, with `A` on whether each is held. -/
def UpdHas (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (A : Prop → Prop → Prop) : Prop :=
  (∃ s, KeyNE den lines ks NK nt nopt md s ∧ A (∃ x, ∃ L ∈ lines, LongM den L s (some x))
      (∃ x, NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (some x))) ∨
    ∃ d ∈ Ds, DomNE den lines nt nopt md d ∧ A (∃ x, ∃ L ∈ lines, LineTag den L d x) (∃ x, NewDom den lines nt md d x)

/-- Whether the box is among the updated maps: when keeping, no update removes the values of a key and no line holds
the empty map; otherwise, some update gives a value. -/
def BoxPresent (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool)
    (md : String) (Ds : List String) : Prop :=
  (md = "keep" → ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∧ ¬n) ∧ ∀ L ∈ lines, ¬InMLine den L wNone) ∧
    (md ≠ "keep" → UpdHas den lines ks NK nt nopt md Ds (fun _ n => n))

/-- Keeping absent keys with no key or kind holding old or new values: the maps are unchanged. -/
def BoxSame (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool)
    (md : String) (Ds : List String) : Prop :=
  md = "keep" ∧ ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∨ n)

/-- The maps `map_update_box/6` gives, for any constant update. -/
def BoxRes (den : Term → V → Prop) (lines : List Term) (ks AK NK : List String) (R : String → Prop) (nt : Term)
    (nopt : Bool) (md : String) (Ds : List String) (w : MW V) : Prop :=
  ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ∧
    (BoxSame den lines ks NK nt nopt md Ds → ∃ L ∈ lines, InMLine den L w) ∧
    (¬BoxSame den lines ks NK nt nopt md Ds → BoxSynG den lines ks NK R nt nopt md Ds w ∧
      (BoxPresent den lines ks NK nt nopt md Ds →
        ((nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → ¬UnsetSemD den ks AK Ds nt w) ∧
        (¬(nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → w ≠ wNone)))

/-- `map_update_box/6` for any constant update. -/
theorem box_runG (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (bdd : Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (fbd : MField E bdd)
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {nt : Term} (hnt : E nt)
    (snt : nt = .atom "term" ∨ ∃ Z, nt = .map Z) (nopt : Bool) {md : String} (hmd : Mode md)
    (ks AK Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ (NK : List String) (R : String → Prop) (res : Term), Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 4)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list (Ds.map Term.atom)) (cOp nt nopt md) (Term.list (AK.map Term.atom)) =
        .ok res ∧ (∀ s ∈ AK, s ∈ NK) ∧
      (∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) ∧ (∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s) ∧
      (∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧ KeyNE den lines ks NK nt nopt md s ∧
        ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s) ∧
      ∃ X, res = .map X ∧ MapsD E den X (BoxRes den lines ks AK NK R nt nopt md Ds) := by
  classical
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨X, NK, rX, rNK, ndNK, saNK, akNK, lnNK, orNK⟩ := box_named (E := E) (n + 1) lines hl' AK
  obtain ⟨P, Q, rPQ, hP, fP, uQ, cQ, nQ, kQ⟩ := box_fields_gen ef hn lines hl hnt nopt hmd ks NK ndNK
  obtain ⟨Q', rQ', subQ', supQ', neQ'⟩ := box_filter_gen ef (m := n + 3) (by omega) Q uQ
  obtain ⟨T, U, rTU, lowT, semT, duU, puU, neU, dgU, cvU⟩ := box_domains_gen ef (n := n + 3) (by omega) lines hl' hnt nopt hmd Ds hD
  have sP : FieldsV E P := by
    refine ⟨fun e me => ?_, ?_⟩
    · obtain ⟨s, e₁, fe, -⟩ := fP e me; exact ⟨⟨s, e₁⟩, fe⟩
    · have := saNK; rw [← hP] at this; exact List.pairwise_map.mp this
  -- The field of a named key over the lines.
  have lookP : ∀ s ∈ NK, ∃ f, mapLookup P (.atom s) = some f ∧ FieldValue E f ∧
      ∀ o, FieldSem den f o ↔ ∃ L ∈ lines, LongM den L s o := fun s ms => by
    have : Term.atom s ∈ P.map Prod.fst := by rw [hP]; exact List.mem_map_of_mem ms
    obtain ⟨e, me, e₁⟩ := List.mem_map.mp this
    obtain ⟨s', e₁', fe, se⟩ := fP e me
    rw [e₁] at e₁'; cases e₁'
    exact ⟨e.2, lookup_of_mem sP me e₁, fe, se⟩
  have noneP : ∀ s, s ∉ NK → mapLookup P (.atom s) = none := fun s ns => by
    cases h : mapLookup P (.atom s) with
    | none => rfl
    | some f =>
      obtain ⟨e, me, e₁, -⟩ := lookup_some_mem h
      have : Term.atom s ∈ NK.map Term.atom := by rw [← hP]; exact List.mem_map.mpr ⟨e, me, e₁⟩
      exact absurd (by simpa using this) ns
  -- The filtered updates are those of the keys whose update gives some field.
  have uQ' : ∀ q ∈ Q', ∃ s, s ∈ ks ∧ s ∈ NK ∧ KeyUpdG E den lines nt nopt md s q := fun q mq => by
    obtain ⟨s, sk, hq⟩ := uQ q (subQ'.subset mq)
    have := kQ q (subQ'.subset mq)
    obtain ⟨old, new, e, rest⟩ := hq
    subst e
    simp only [updKey, List.mem_map, Term.atom.injEq, exists_eq_right] at this
    exact ⟨s, sk, this, old, new, rfl, rest⟩
  have memQ' : ∀ s, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new]) ↔ KeyNE den lines ks NK nt nopt md s := by
    intro s
    constructor
    · rintro ⟨q, mq, old, new, rfl⟩
      obtain ⟨s', sk, ms, old', new', e', -, sold, -, snew⟩ := uQ' _ mq
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      subst e₂ e₃
      obtain ⟨o, ho⟩ := neQ' _ mq
      refine ⟨ms, sk, o, ?_⟩
      have := (snew o).mp ho
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      rwa [eqF] at this
    · rintro ⟨ms, sk, o, ho⟩
      obtain ⟨q, mq, old, new, rfl, -, sold, -, snew⟩ := cQ s ms sk
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      have hn : FieldSem den new o := (snew o).mpr (by rw [eqF]; exact ho)
      exact ⟨_, supQ' _ mq ⟨o, hn⟩, old, new, rfl⟩
  have ndQ' : (Q'.map updKey).Nodup := (subQ'.map updKey).nodup nQ
  -- Replacing: rejecting with a single key update and no domain update.
  let rep : Prop := md = "reject" ∧ U = [] ∧ ∃ q, Q' = [q]
  let R : String → Prop := fun s => rep ∧ ∃ old new, Q' = [.tuple #[.atom s, old, new]]
  have hR : ∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧
      KeyNE den lines ks NK nt nopt md s ∧ ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s := by
    intro s
    have eU : U = [] ↔ ∀ d ∈ Ds, ¬DomNE den lines nt nopt md d := by
      exact ⟨fun h d md hd => (neU.mpr ⟨d, md, hd⟩) h,
        fun h => Classical.byContradiction fun ne => let ⟨d, md, hd⟩ := neU.mp ne; h d md hd⟩
    constructor
    · rintro ⟨⟨hr, hU, -⟩, old, new, hq⟩
      refine ⟨hr, eU.mp hU, (memQ' s).mp ⟨_, by rw [hq]; simp, old, new, rfl⟩, fun s' h' => ?_⟩
      obtain ⟨q, mq, old', new', rfl⟩ := (memQ' s').mpr h'
      rw [hq, List.mem_singleton] at mq
      obtain ⟨e₁, -, -⟩ := tuple3_inj mq
      exact Term.atom.inj e₁
    · rintro ⟨hr, hU, hs, uniq⟩
      obtain ⟨q, mq, old, new, rfl⟩ := (memQ' s).mpr hs
      have single : Q' = [.tuple #[.atom s, old, new]] := by
        have all : ∀ q' ∈ Q', q' = .tuple #[.atom s, old, new] → True := fun _ _ _ => trivial
        clear all
        obtain ⟨pre, suf, rfl⟩ := List.append_of_mem mq
        have keyOf : ∀ q' ∈ pre ++ suf, updKey q' = .atom s := fun q' m' => by
          have m'' : q' ∈ pre ++ Term.tuple #[.atom s, old, new] :: suf := by
            rcases List.mem_append.mp m' with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          obtain ⟨s', -, -, old', new', rfl, -⟩ := uQ' _ m''
          have := uniq s' ((memQ' s').mp ⟨_, m'', old', new', rfl⟩)
          simp [updKey, this]
        have nd := ndQ'
        simp only [List.map_append, List.map_cons] at nd
        have hpre : pre = [] := by
          cases pre with
          | nil => rfl
          | cons p ps =>
            exfalso
            have := (List.nodup_append.mp nd).2.2 (updKey p) (by simp) (updKey (.tuple #[.atom s, old, new]))
              List.mem_cons_self
            exact this (by rw [keyOf p (by simp)]; simp [updKey])
        have hsuf : suf = [] := by
          cases suf with
          | nil => rfl
          | cons p ps =>
            exfalso
            subst hpre
            have := (List.nodup_cons.mp nd).1
            exact this (by rw [show updKey (.tuple #[.atom s, old, new]) = updKey p by
              rw [keyOf p (by simp)]; simp [updKey]]; simp)
        subst hpre hsuf; rfl
      exact ⟨⟨hr, eU.mpr hU, _, single⟩, old, new, single⟩
  -- The fields of the box, with the updates.
  obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ : ∃ P2, Erlang.lists.«foldl/3» (D (n + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-11-" 2 #[boolAtom (decide rep)])
      (fieldsTerm P) (Term.list Q') = .ok (fieldsTerm P2) ∧ FieldsV E P2 ∧
      (∀ s, mapLookup P2 (.atom s) = none ↔ mapLookup P (.atom s) = none) ∧
      ∀ s o, (∃ f, mapLookup P2 (.atom s) = some f ∧ FieldSem den f o) ↔
        ((¬R s ∧ ∃ f, mapLookup P (.atom s) = some f ∧ FieldSem den f o) ∨
          ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) := by
    by_cases hrep : rep
    · have hrep' := hrep
      obtain ⟨-, -, q, hq⟩ := hrep
      obtain ⟨s₀, -, ms₀, old, new, rfl, -, sold, fnew, -⟩ := uQ' q (by rw [hq]; simp)
      obtain ⟨P2, rP2, sP2, l₀, lo⟩ := box_store_rep (m := n + 3) sP (s := s₀) (old := old) fnew
      refine ⟨P2, by rw [decide_eq_true hrep', hq]; exact rP2, sP2, fun s => ?_, fun s o => ?_⟩
      · by_cases e : s = s₀
        · subst e; obtain ⟨f, lf, -⟩ := lookP s ms₀; simp [l₀, lf]
        · rw [lo s e]
      · have Rs : R s ↔ s = s₀ := ⟨fun ⟨_, old', new', h⟩ => by
            rw [hq] at h; simp at h; exact h.1.symm,
          fun e => ⟨hrep', old, new, by rw [hq, e]⟩⟩
        by_cases e : s = s₀
        · subst e
          rw [l₀]
          simp only [Option.some.injEq, exists_eq_left', hq, List.mem_singleton]
          constructor
          · intro h; exact Or.inr ⟨_, rfl, old, new, rfl, h⟩
          · rintro (⟨nr, -⟩ | ⟨q', rfl, old', new', e', h⟩)
            · exact absurd (Rs.mpr rfl) nr
            · obtain ⟨-, -, rfl⟩ := tuple3_inj e'; exact h
        · rw [lo s e, Rs]
          simp only [e, not_false_eq_true, true_and, hq, List.mem_singleton]
          constructor
          · exact Or.inl
          · rintro (h | ⟨q', rfl, old', new', e', -⟩)
            · exact h
            · obtain ⟨e₁, -, -⟩ := tuple3_inj e'; exact absurd (Term.atom.inj e₁).symm e
    · obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ := box_store ef (m := n + 3) (by omega) sP Q' (fun q mq => by
          obtain ⟨s, -, ms, old, new, rfl, hold, sold, hnew, -⟩ := uQ' q mq
          obtain ⟨f, lf, -, sf⟩ := lookP s ms
          exact ⟨s, old, new, rfl, hold, hnew, f, lf, fun o => (sold o).trans (sf o).symm⟩) ndQ'
      have nR : ∀ s, ¬R s := fun s h => hrep h.1
      refine ⟨P2, by rw [decide_eq_false hrep]; exact rP2, sP2, keysP2, fun s o => ?_⟩
      rw [lookP2]
      simp [nR s]
  -- The tag, open when every kind holds `term()`.
  have gT := lowTag_tagV lowT
  let T2 := if Term.compare (Term.fuel T allTerm) T allTerm = .eq then Term.atom "open" else T
  have gT2 : TagV E T2 := by
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte]; exact Or.inl rfl
    · simp only [T2, e, ↓reduceIte]; exact gT
  have semT2 : ∀ kind ∈ domainKinds, ∀ x, den (tagType T2 kind) x ↔ BoxTagG den lines nt md Ds kind x := by
    intro kind mk x
    rw [← semT kind mk x]
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte, tagType]
      exact ⟨fun _ => allTerm_full ef gT e kind mk x, fun _ => ef.den_term x⟩
    · simp only [T2, e, ↓reduceIte]
  obtain ⟨bo, rbo, fbo, sbo⟩ := map_new_leaf (den := den) ef gT2 sP2
  have semNew : ∀ s ∈ NK, ∀ o, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) ↔
      s ∈ ks ∧ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) o := fun s ms o => by
    constructor
    · rintro ⟨q, mq, old, new, rfl, hq⟩
      obtain ⟨s', ks', -, old', new', e', -, sold', -, snew'⟩ := uQ' _ mq
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      subst e₂ e₃
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold' o)
      exact ⟨ks', by rw [← eqF]; exact (snew' o).mp hq⟩
    · rintro ⟨sk, ho⟩
      obtain ⟨q, mq, old, new, rfl, -, sold, -, snew⟩ := cQ s ms sk
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      have hn : FieldSem den new o := (snew o).mpr (by rw [eqF]; exact ho)
      exact ⟨_, supQ' _ mq ⟨o, hn⟩, old, new, rfl, hn⟩
  have semBo : ∀ w, MSem den T2 P2 w ↔ BoxSynG den lines ks NK R nt nopt md Ds w := fun w => by
    rw [msem_keys]
    constructor
    · intro h
      refine ⟨fun s ms => ?_, fun s ns => ?_, fun k i => ?_⟩
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        obtain ⟨f, lf, -, sf⟩ := lookP s ms
        cases l2 : mapLookup P2 (.atom s) with
        | none => exact absurd ((keysP2 s).mp l2) (by simp [lf])
        | some f2 =>
          rw [l2] at this
          rcases (lookP2 s _).mp ⟨f2, l2, this⟩ with ⟨nr, f', lf', h'⟩ | h'
          · rw [lf] at lf'; cases lf'; exact Or.inl ⟨nr, (sf _).mp h'⟩
          · exact Or.inr ((semNew s ms _).mp h')
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        rw [(keysP2 s).mpr (noneP s ns)] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mp hx⟩
      · have := h (.dom k i)
        simp only [KeyAllow] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mp hx⟩
    · rintro ⟨hn, hu, hd⟩ q
      cases q with
      | atom s =>
        simp only [KeyAllow, FSem]
        by_cases ms : s ∈ NK
        · obtain ⟨f, lf, -, sf⟩ := lookP s ms
          have hf : (¬R s ∧ ∃ f', mapLookup P (.atom s) = some f' ∧ FieldSem den f' (w (.atom s))) ∨
              ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new (w (.atom s)) := by
            rcases hn s ms with ⟨nr, h'⟩ | h'
            · exact Or.inl ⟨nr, f, lf, (sf _).mpr h'⟩
            · exact Or.inr ((semNew s ms _).mpr h')
          obtain ⟨f2, l2, h2⟩ := (lookP2 s _).mpr hf
          rw [l2]; exact h2
        · rw [(keysP2 s).mpr (noneP s ms)]
          simp only
          rw [tagSem_iff ef gT2]
          rcases hu s ms with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mpr hx⟩
      | dom k i =>
        simp only [KeyAllow]
        rw [tagSem_iff ef gT2]
        rcases hd k i with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mpr hx⟩
  -- The pairs of old and new types of the updates.
  have shQ : ∀ q ∈ Q', ∃ s ot oo t' o', q = .tuple #[.atom s, .tuple #[ot, oo], .tuple #[t', o']] ∧
      KeyNE den lines ks NK nt nopt md s ∧ E ot ∧ E t' ∧ (∀ x, den ot x ↔ ∃ L ∈ lines, LongM den L s (some x)) ∧
      ∀ x, den t' x ↔ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (some x) := by
    intro q mq
    obtain ⟨s, -, -, old, new, rfl, ⟨ot, oo, rfl, hot⟩, sold, ⟨t', o', rfl, ht'⟩, snew⟩ := uQ' q mq
    have eqF : FieldSem den (.tuple #[ot, boolAtom oo]) = fun o => ∃ L ∈ lines, LongM den L s o :=
      funext fun o => propext (sold o)
    refine ⟨s, ot, boolAtom oo, t', boolAtom o', rfl, (memQ' s).mp ⟨_, mq, _, _, rfl⟩, hot, ht', fun x => ?_,
      fun x => ?_⟩
    · rw [← sold (some x), fieldSem_mk]; simp
    · have := snew (some x)
      rw [eqF] at this
      rw [← this, fieldSem_mk]; simp
  have rKP := keyPair_eval (n + 4) Q' fun q mq => by
    obtain ⟨s, ot, oo, t', o', e, -⟩ := shQ q mq; exact ⟨_, _, _, _, _, e⟩
  have rDP := domPair_eval (n + 4) U fun u mu => by
    obtain ⟨d, o, t, e, -⟩ := dgU u mu; exact ⟨_, _, _, e⟩
  have rAp := append_list (Q'.map keyPair) (U.map domPair)
  have upsE : ∀ p ∈ Q'.map keyPair ++ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧ E o ∧ E n' := by
    intro p mp
    rcases List.mem_append.mp mp with mp | mp
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
      obtain ⟨s, ot, oo, t', o', rfl, -, hot, ht', -⟩ := shQ q mq
      exact ⟨ot, t', by simp [keyPair], hot, ht'⟩
    · obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, o, t, rfl, -, -, ho, ht, -⟩ := dgU u mu
      exact ⟨o, t, by simp [domPair], ho, ht⟩
  -- The pairs hold what the named keys and kinds updated hold.
  have upsHas : ∀ A : Prop → Prop → Prop, (∃ p ∈ Q'.map keyPair ++ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧
      A (∃ x, den o x) (∃ x, den n' x)) ↔ UpdHas den lines ks NK nt nopt md Ds A := by
    intro A
    constructor
    · rintro ⟨p, mp, o, n', e, h⟩
      rcases List.mem_append.mp mp with mp | mp
      · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
        obtain ⟨s, ot, oo, t', o', rfl, hk, -, -, so, sn⟩ := shQ q mq
        simp only [keyPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [propext (exists_congr so), propext (exists_congr sn)] at h
        exact Or.inl ⟨s, hk, h⟩
      · obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
        obtain ⟨d, o', t, rfl, md', hne, -, -, so, sn⟩ := dgU u mu
        simp only [domPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [propext (exists_congr so), propext (exists_congr sn)] at h
        exact Or.inr ⟨d, md', hne, h⟩
    · rintro (⟨s, hk, h⟩ | ⟨d, md', hne, h⟩)
      · obtain ⟨q, mq, old, new, rfl⟩ := (memQ' s).mpr hk
        obtain ⟨s', ot, oo, t', o', e, -, -, -, so, sn⟩ := shQ _ mq
        obtain ⟨e1, rfl, rfl⟩ := tuple3_inj e
        cases Term.atom.inj e1
        rw [← propext (exists_congr so), ← propext (exists_congr sn)] at h
        exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem mq), ot, t', by simp [keyPair], h⟩
      · obtain ⟨u, mu, o, t, rfl⟩ := cvU d md' hne
        obtain ⟨d', o', t', e, -, -, -, -, so, sn⟩ := dgU _ mu
        obtain ⟨e1, rfl, rfl⟩ := tuple3_inj e
        cases Term.atom.inj e1
        rw [← propext (exists_congr so), ← propext (exists_congr sn)] at h
        exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem mu), o, t, by simp [domPair], h⟩
  -- Keeping with no old or new values: unchanged.
  obtain ⟨ba, ra, sa⟩ : ∃ ba : Bool, Erlang.lists.«all/2» (D (n + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-fun-10-" 1 #[])
      (Term.list (Q'.map keyPair ++ U.map domPair)) = .ok (boolAtom ba) ∧
      (ba = Bool.true ↔ ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∨ n)) := by
    classical
    let res : Term → Bool := fun p => decide (∃ o n', p = .tuple #[o, n'] ∧ ¬((∃ x, den o x) ∨ ∃ x, den n' x))
    refine ⟨_, all_list _ _ _ _ res _ fun p mp => ?_, ?_⟩
    · obtain ⟨o, n', rfl, ho, hn'⟩ := upsE p mp
      obtain ⟨eo, reo, seo⟩ := ef.empty1 (m := n + 3) (by omega) ho
      obtain ⟨en, ren, sen⟩ := ef.empty1 (m := n + 3) (by omega) hn'
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-10-/1».pure]
      have hP : (∃ o' n'', Term.tuple #[o, n'] = .tuple #[o', n''] ∧ ¬((∃ x, den o' x) ∨ ∃ x, den n'' x)) ↔
          (eo = Bool.true ∧ en = Bool.true) := by
        constructor
        · rintro ⟨o', n'', e, h⟩
          obtain ⟨rfl, rfl⟩ : o = o' ∧ n' = n'' := by simpa using e
          exact ⟨seo.mpr fun x hx => h (Or.inl ⟨x, hx⟩), sen.mpr fun x hx => h (Or.inr ⟨x, hx⟩)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨o, n', rfl, fun h => h.elim (fun ⟨x, hx⟩ => seo.mp h1 x hx) (fun ⟨x, hx⟩ => sen.mp h2 x hx)⟩
      have dec : res (.tuple #[o, n']) = (eo && en) := by
        cases h : (eo && en)
        · exact decide_eq_false fun hh => by
            have := hP.mp hh; rw [this.1, this.2] at h; cases h
        · exact decide_eq_true (hP.mpr (by cases eo <;> cases en <;> simp_all))
      rw [dec]
      cases eo <;> cases en <;>
        simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-10-/1», reo, ren, Lynx.Except.andAlso, boolAtom]
    · rw [List.all_eq_true, ← upsHas]
      constructor
      · rintro h ⟨p, mp, o, n', e, hh⟩
        obtain ⟨o', n'', e', hn⟩ := of_decide_eq_true (h p mp)
        rw [e] at e'
        obtain ⟨rfl, rfl⟩ : o = o' ∧ n' = n'' := by simpa using e'
        exact hn hh
      · intro h p mp
        apply decide_eq_true
        obtain ⟨o, n', rfl, -, -⟩ := upsE p mp
        exact ⟨o, n', rfl, fun hh => h ⟨_, mp, o, n', rfl, hh⟩⟩
  obtain ⟨bp, rbp, sbp⟩ := present_gen (den := den) ef (m := n + 1) (by omega) lines hl' nt nopt hmd
    (Q'.map keyPair ++ U.map domPair) upsE
  have present : bp = Bool.true ↔ BoxPresent den lines ks NK nt nopt md Ds := by
    rw [sbp]
    unfold BoxPresent
    have k1 := upsHas (fun o n => o ∧ ¬n)
    have k2 := upsHas (fun _ n => n)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun hu => (h1 hk).1 ?_, (h1 hk).2⟩, fun hk => k2.mp (h2 hk)⟩
      obtain ⟨p, mp, o, n', e, ho, hn⟩ := k1.mpr hu
      exact ⟨p, mp, o, n', e, fun x hx => hn ⟨x, hx⟩, ho⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun ⟨p, mp, o, n', e, hn, ho⟩ => (h1 hk).1 (k1.mp ⟨p, mp, o, n', e, ho, fun ⟨x, hx⟩ => hn x hx⟩),
        (h1 hk).2⟩, fun hk => k2.mpr (h2 hk)⟩
  obtain ⟨bu, rbu, fbu, sbu⟩ := box_unsetD ef (m := n + 2) (by omega) ks AK Ds hD hnt snt
  obtain ⟨r, rr, hr⟩ := map_opt_diff1 (den := den) ef (m := n + 2) (by omega) fbo fbu
  have rTU' := rTU
  simp only [domainKinds, List.map] at rTU'
  have rAll : Erlang.lists.«map/2» (D (n + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_box/6-anonymous-0-" 1 #[])
      (Term.list (domainKinds.map Term.atom)) = .ok allTerm := by
    have := all_term_run _ (Or.inl rfl) (n + 3)
    rwa [usort_sorted _ kinds_sa, Lynx.Except.ok_bind] at this
  have uK := usort_sorted _ kinds_sa
  simp only [domainKinds, List.map] at rAll uK
  have rT2 : Erlang.erlang.«==/2» T allTerm = .ok (boolAtom (Term.compare (Term.fuel T allTerm) T allTerm == .eq)) :=
    eqq_val T allTerm
  have eQ := eqq_val (Term.list Q') .nil
  have eU := eqq_val (Term.list U) .nil
  have Q0 : Q' = [] ↔ ¬∃ s, KeyNE den lines ks NK nt nopt md s := by
    constructor
    · rintro e ⟨s, hs⟩
      obtain ⟨q, mq, -⟩ := (memQ' s).mpr hs
      rw [e] at mq; cases mq
    · intro h
      cases hq : Q' with
      | nil => rfl
      | cons q qs =>
        obtain ⟨s, -, -, old, new, rfl, -⟩ := uQ' q (by rw [hq]; simp)
        exact absurd ⟨s, (memQ' s).mp ⟨_, by rw [hq]; simp, old, new, rfl⟩⟩ h
  have U0 : U = [] ↔ ¬∃ d ∈ Ds, DomNE den lines nt nopt md d := by
    constructor
    · intro e h; exact (neU.mpr h) e
    · intro h; exact Classical.byContradiction fun ne => h (neU.mp ne)
  -- The run, given its result.
  have run : ∀ res, (Q' = [] ∧ U = [] → res = .map []) →
      (¬(Q' = [] ∧ U = []) → BoxSame den lines ks NK nt nopt md Ds → res = .map [(.atom "map", bdd)]) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → ¬BoxPresent den lines ks NK nt nopt md Ds →
        res = .map [(.atom "map", bo)]) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → BoxPresent den lines ks NK nt nopt md Ds →
        nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12 → .ok res = Elixir.Module.Types.Descr.«opt_difference/2» (D (n + 4))
          (.map [(.atom "map", bo)]) (.map [(.atom "map", bu)])) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → BoxPresent den lines ks NK nt nopt md Ds →
        ¬(nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → .ok res = (do
          let a ← Elixir.Module.Types.Descr.«map_update_domains_add/3» (D (n + 4)) bo (fieldsTerm P2)
            (.tuple #[.nil, .nil])
          Elixir.Module.Types.Descr.«map_update_domains_result/1» (D (n + 4)) a)) →
      Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 4)) bdd (Term.list lines) (Term.list (ks.map Term.atom))
        (Term.list (Ds.map Term.atom)) (cOp nt nopt md) (Term.list (AK.map Term.atom)) = .ok res := by
    intro res c0 cS c1 c2 c3
    have lenD : Erlang.erlang.«length/1» (Term.list (Ds.map Term.atom)) = .ok (.integer (Ds.length : Int)) := by
      simpa using length_list (Ds.map Term.atom)
    have cmpNil : ∀ l : List Term, (Term.compare ((Term.list l).fuel .nil) (Term.list l) .nil == .eq) =
        decide (l = []) := fun l => by
      cases l with
      | nil => simp [Term.list, Lynx.Term.compare_self]
      | cons x xs => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
    unfold Elixir.Module.Types.Descr.«map_update_box/6»
    simp [rX, rNK, rPQ, rQ', rTU', rKP, rDP, rAp, Lynx.Except.andAlso, Erlang.erlang.«element/2», uK, rAll, rT2,
      cmpNil, eqq_val]
    have same : BoxSame den lines ks NK nt nopt md Ds ↔ md = "keep" ∧ ba = Bool.true := by
      rw [BoxSame, sa]
    by_cases h0 : Q' = [] ∧ U = []
    · rw [c0 h0]; obtain ⟨rfl, rfl⟩ := h0; simp [boolAtom]
    have hd : (decide (Q' = []) && decide (U = [])) = Bool.false := by
      cases h : (decide (Q' = []) && decide (U = []))
      · rfl
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        exact absurd h h0
    rw [hd]
    simp only [boolAtom, Bool.false_eq_true, ↓reduceIte]
    by_cases hS : BoxSame den lines ks NK nt nopt md Ds
    · rw [cS h0 hS]
      obtain ⟨rfl, rfl⟩ := same.mp hS
      simp [ra, boolAtom, Erlang.erlang.«/=/2»]
    · have ba_f : md = "keep" → ba = Bool.false := fun hk => by
        cases h : ba
        · rfl
        · exact absurd (same.mpr ⟨hk, h⟩) hS
      rcases hmd with rfl | rfl | rfl
      · simp [Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        have dr : decide rep = Bool.false := decide_eq_false fun ⟨h, _⟩ => by simp at h
        rw [dr] at rP2
        simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
        by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
          simp only [T2, e, ↓reduceIte] at rbo <;>
          simp [e, rP2, rbo, rbp] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
        all_goals first
          | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
          | (have hp := present.mp (by simp)
             by_cases hu : nopt = Bool.false ∧ "force" ≠ "keep" ∧ Ds.length ≠ 12
             · have c2' := c2 h0 hS hp hu
               obtain ⟨rfl, hk, hL⟩ := hu
               first
                 | exact absurd rfl hk
                 | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                    simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
             · have c3' := c3 h0 hS hp hu
               cases nopt <;> simp [cOp, boolAtom, lenD] at hu ⊢ <;>
                 first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                           simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
        all_goals done
      · rw [ba_f rfl] at ra
        simp [ra, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        have dr : decide rep = Bool.false := decide_eq_false fun ⟨h, _⟩ => by simp at h
        rw [dr] at rP2
        simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
        by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
          simp only [T2, e, ↓reduceIte] at rbo <;>
          simp [e, rP2, rbo, rbp] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
        all_goals first
          | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
          | (have hp := present.mp (by simp)
             by_cases hu : nopt = Bool.false ∧ "keep" ≠ "keep" ∧ Ds.length ≠ 12
             · have c2' := c2 h0 hS hp hu
               obtain ⟨rfl, hk, hL⟩ := hu
               first
                 | exact absurd rfl hk
                 | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                    simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
             · have c3' := c3 h0 hS hp hu
               cases nopt <;> simp [cOp, boolAtom] at hu ⊢ <;>
                 first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                           simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
        all_goals done
      · simp [Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        split
        · rename_i q₀ e₁ e₂ _
          have eQ1 : Q' = [q₀] := list_inj (e₁.trans rfl)
          have eU1 : U = [] := list_inj (e₂.trans rfl)
          have dr : decide rep = Bool.true := decide_eq_true ⟨rfl, eU1, q₀, eQ1⟩
          rw [dr] at rP2
          simp only [boolAtom, ↓reduceIte] at rP2
          by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
            simp only [T2, e, ↓reduceIte] at rbo <;>
            simp [e, rP2, rbo, rbp] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
          all_goals first
            | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
            | (have hp := present.mp (by simp)
               by_cases hu : nopt = Bool.false ∧ "reject" ≠ "keep" ∧ Ds.length ≠ 12
               · have c2' := c2 h0 hS hp hu
                 obtain ⟨rfl, hk, hL⟩ := hu
                 first
                   | exact absurd rfl hk
                   | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                      simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
               · have c3' := c3 h0 hS hp hu
                 cases nopt <;> simp [cOp, boolAtom, lenD] at hu ⊢ <;>
                   first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                             simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
          all_goals done

        · rename_i hnot
          have dr : decide rep = Bool.false := decide_eq_false fun ⟨_, eU1, q, eQ1⟩ =>
            hnot q (by rw [eQ1]) (by rw [eU1]) rfl
          rw [dr] at rP2
          simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
          by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
            simp only [T2, e, ↓reduceIte] at rbo <;>
            simp [e, rP2, rbo, rbp] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
          all_goals first
            | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
            | (have hp := present.mp (by simp)
               by_cases hu : nopt = Bool.false ∧ "reject" ≠ "keep" ∧ Ds.length ≠ 12
               · have c2' := c2 h0 hS hp hu
                 obtain ⟨rfl, hk, hL⟩ := hu
                 first
                   | exact absurd rfl hk
                   | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                      simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
               · have c3' := c3 h0 hS hp hu
                 cases nopt <;> simp [cOp, boolAtom, lenD] at hu ⊢ <;>
                   first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                             simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
          all_goals done
  have congr : ∀ {X : List (Term × Term)} {S S' : MW V → Prop}, MapsD E den X S → (∀ w, S w ↔ S' w) →
      MapsD E den X S' := fun h e => ⟨h.1, h.2.1, fun w => (h.2.2 w).trans (e w)⟩
  have upd : ¬(Q' = [] ∧ U = []) → ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) :=
    fun h0 => Classical.byContradiction fun h => h0 ⟨Q0.mpr fun e => h (Or.inl e), U0.mpr fun e => h (Or.inr e)⟩
  by_cases h0 : Q' = [] ∧ U = []
  · refine ⟨NK, R, .map [], run _ (fun _ => rfl) (fun h => absurd h0 h) (fun h => absurd h0 h) (fun h => absurd h0 h)
      (fun h => absurd h0 h), akNK, lnNK, orNK, hR, [], rfl, mapsD_nil fun w hw => ?_⟩
    rcases hw.1 with h | h
    · exact (Q0.mp h0.1) h
    · exact (U0.mp h0.2) h
  have up := upd h0
  by_cases hS : BoxSame den lines ks NK nt nopt md Ds
  · refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ _ => rfl) (fun _ h => absurd hS h) (fun _ h => absurd hS h)
      (fun _ h => absurd hS h), akNK, lnNK, orNK, hR, _, rfl, mapsD_field fbd fun w => ?_⟩
    rw [sbd]
    exact ⟨fun h => ⟨up, fun _ => h, fun h' => absurd hS h'⟩, fun h => h.2.1 hS⟩
  by_cases hp : BoxPresent den lines ks NK nt nopt md Ds
  · by_cases hu : nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12
    · obtain ⟨X', eX, mX⟩ := mapsD_box (E := E) (den := den) (res := r) (S := BoxRes den lines ks AK NK R nt nopt md Ds) (by
        rcases hr with ⟨rfl, emp⟩ | ⟨c, rfl, fc, sc⟩
        · refine Or.inl ⟨rfl, fun w ⟨_, _, hq⟩ => ?_⟩
          have := emp w
          rw [(sbo w).mpr ((semBo w).mpr (hq hS).1)] at this
          cases h : denMF E den bu w
          · rw [h] at this; cases this
          · exact ((hq hS).2 hp).1 hu ((sbu w).mp h)
        · refine Or.inr ⟨c, bo, rfl, fc, fun w => ?_⟩
          rw [sc, Bool.and_eq_true, Bool.not_eq_true', sbo, semBo]
          constructor
          · rintro ⟨hb, hu'⟩
            refine ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun _ h => ?_, fun h => absurd hu h⟩⟩⟩
            rw [(sbu w).mpr h] at hu'
            simp at hu'
          · rintro ⟨-, -, hq⟩
            refine ⟨(hq hS).1, ?_⟩
            cases h : denMF E den bu w
            · rfl
            · exact absurd ((sbu w).mp h) (((hq hS).2 hp).1 hu))
      exact ⟨NK, R, r, run r (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
        (fun _ _ _ _ => rr.symm) (fun _ _ _ h => absurd hu h), akNK, lnNK, orNK, hR, X', eX, mX⟩
    · rcases domains_add (E := E) (n + 3) bo sP2 [] [] with ⟨rda, req⟩ | ⟨rda, nreq⟩
      · obtain ⟨X', rX', mX⟩ := domains_result (den := den) ef (m := n + 2) (by omega) [] [bo] (by simp)
          (fun b mb => by simp at mb; subst mb; exact fbo)
        refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
          (fun _ _ _ h => absurd h hu) (fun _ _ _ _ => by rw [rda]; simpa using rX'.symm), akNK, lnNK, orNK, hR, X',
          rfl, congr mX fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_or, List.mem_singleton, exists_eq_left]
        rw [sbo, semBo]
        exact ⟨fun hb => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun h => absurd h hu, fun _ =>
          msem_req_ne_none sP2 req ((semBo w).mpr hb)⟩⟩⟩, fun h => (h.2.2 hS).1⟩
      · obtain ⟨X', rX', mX⟩ := domains_result (den := den) ef (m := n + 2) (by omega) [bo] []
          (fun b mb => by simp at mb; subst mb; exact fbo) (by simp)
        refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
          (fun _ _ _ h => absurd h hu) (fun _ _ _ _ => by rw [rda]; simpa using rX'.symm), akNK, lnNK, orNK, hR, X',
          rfl, congr mX fun w => ?_⟩
        simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, false_and, exists_false, or_false]
        rw [sbo, semBo]
        exact ⟨fun ⟨hb, hn⟩ => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun h => absurd h hu, fun _ => hn⟩⟩⟩,
          fun ⟨_, _, hq⟩ => ⟨(hq hS).1, ((hq hS).2 hp).2 hu⟩⟩
  · refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ _ => rfl) (fun _ _ h => absurd h hp)
      (fun _ _ h => absurd h hp), akNK, lnNK, orNK, hR, _, rfl, mapsD_field fbo fun w => ?_⟩
    rw [sbo, semBo]
    exact ⟨fun hb => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun h => absurd h hp⟩⟩, fun h => (h.2.2 hS).1⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! `map_update_widen/3` for any constant update: the chain of `widen_line`, with the values a kind gets given by a
predicate `P` on kinds instead of a value. -/

/-- A domain update of `map_update_widen/3`: a kind, the tag's type there, and the new type, holding the values `P`
gives the kind. -/
def DomUpdP (E : Term → Prop) (den : Term → V → Prop) (tag : Term) (P : String → V → Prop) (d : String) (u : Term) :
    Prop :=
  ∃ nt, u = .tuple #[.atom d, tagType tag d, nt] ∧ E nt ∧ ∀ x, den nt x ↔ P d x

/-- A step of `map_widen_domains/3`: on negations, `discard` when the tag misses some old values, otherwise the kind
widened by the new type. -/
theorem widen_stepP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL acc : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) (gA : TagV E acc) {d : String} (hd : d ∈ domainKinds) {P : String → V → Prop} {nt : Term} (hnt : E nt)
    (snt : ∀ x, den nt x ↔ P d x) (neg : Bool) :
    (neg = Bool.true ∧ ¬SubAt den tagL tag0 d ∧
      (D (m + 2)).pure (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .error (.throw (.atom "discard"))) ∨
    ((neg = Bool.true → SubAt den tagL tag0 d) ∧ ∃ A, (D (m + 2)).pure
        (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .ok A ∧ TagV E A ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
        if kind = d then den (tagType tag0 d) x ∨ P d x else den (tagType acc kind) x) := by
  have pureE : ∀ a, (D (m + 2)).pure (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2
      #[tag0, boolAtom neg]) #[.tuple #[.atom d, tagType tagL d, nt], a] =
      Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4» (D (m + 1)) tag0 (boolAtom neg)
        (Term.tuple #[.atom d, tagType tagL d, nt]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_widen_domains/3-fun-0-/2».pure]
  obtain ⟨sb, rsb, hsb⟩ := ef.sub (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d)
  have sbI : sb = Bool.true ↔ SubAt den tagL tag0 d := ⟨hsb, fun h => by
    have := ef.subc (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d) h (m + 1) (by omega)
    rw [rsb (m + 1) (by omega)] at this; cases sb <;> simp_all [boolAtom]⟩
  obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] (tagType_value ef.mopsE g0 d) hnt (m := m + 1) (by omega)
  obtain ⟨A, rA, gA', sA⟩ := replace_domain_any ef gA hd hc m
  by_cases bad : neg = Bool.true ∧ sb = Bool.false
  · obtain ⟨rfl, rfl⟩ := bad
    refine Or.inl ⟨rfl, fun h => absurd (sbI.mpr h) (by simp), ?_⟩
    rw [pureE, widen_dom_eval g0]
    simp [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1», Lynx.Term.isMember]
  · refine Or.inr ⟨fun hn => sbI.mp (by cases sb <;> simp_all), A, ?_, gA', fun kind mk x => ?_⟩
    · rw [pureE]
      rw [widen_dom_eval g0]
      cases neg <;> cases sb <;> simp_all [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1»,
        Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2»]
    · rw [sA kind mk x]
      by_cases k : kind = d
      · subst k; simp [sc, snt]
      · simp [k]


/-- The fold of `map_widen_domains/3` over the updates of some kinds: `discard` on negations missing old values,
otherwise the tag with the kinds widened by the value. -/
theorem widen_foldP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {P : String → V → Prop} (neg : Bool) :
    ∀ (Ds : List String) (U : List Term) (done : List String) (acc : Term), U.length = Ds.length →
      (∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) → (∀ d ∈ Ds, d ∈ domainKinds) → TagV E acc →
      (∀ kind ∈ domainKinds, ∀ x, den (tagType acc kind) x ↔
        if kind ∈ done then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x) →
      ((neg = Bool.true ∧ ∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .error (.throw (.atom "discard"))) ∨
      ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ ∃ r, Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .ok r ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ done ++ Ds then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x)
  | [], U, done, acc, lU, _, _, gA, sA => by
    obtain rfl : U = [] := List.eq_nil_of_length_eq_zero (by simpa using lU)
    exact Or.inr ⟨by simp, acc, by simp [Erlang.lists.«foldl_1/3»], gA, by simpa using sA⟩
  | d :: Ds, [], _, _, lU, _, _, _, _ => by simp at lU
  | d :: Ds, u :: U, done, acc, lU, fU, hD, gA, sA => by
    obtain ⟨nt, eu, hnt, snt⟩ := fU (d, u) (by simp)
    simp only at eu
    subst eu
    have hd := hD d (by simp)
    have fU' : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2 := fun p mp => fU p (by simp [mp])
    have hD' : ∀ d ∈ Ds, d ∈ domainKinds := fun d' md => hD d' (by simp [md])
    rcases widen_stepP ef hm g0 gL gA hd hnt snt neg with ⟨hn, hs, run⟩ | ⟨hs, A, run, gA', sA'⟩
    · refine Or.inl ⟨⟨hn, d, by simp, hs⟩, ?_⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only at run ⊢
      simp [run]
    · have sA'' : ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
          if kind ∈ done ++ [d] then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x := by
        intro kind mk x
        rw [sA' kind mk x]
        by_cases k : kind = d
        · subst k; simp
        · rw [sA kind mk x]; simp [k]
      rcases widen_foldP ef hm g0 gL neg Ds U (done ++ [d]) A (by simpa using lU) fU' hD' gA' sA'' with
        ⟨⟨hn, d', md', hs'⟩, rr⟩ | ⟨hs', r, rr, gr, sr⟩
      · refine Or.inl ⟨⟨hn, d', by simp [md'], hs'⟩, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at run rr ⊢
        simp [run, rr]
      · refine Or.inr ⟨fun hn d' md' => ?_, r, ?_, gr, fun kind mk x => by simpa using sr kind mk x⟩
        · rcases List.mem_cons.mp md' with rfl | md'
          · exact hs hn
          · exact hs' hn d' md'
        · rw [Erlang.lists.«foldl_1/3».eq_def]
          simp only at run rr ⊢
          simp [run, rr]


/-- `map_widen_domains/3` on the updates of some kinds. -/
theorem widen_tagP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {P : String → V → Prop} (neg : Bool) (Ds : List String) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ r, Elixir.Module.Types.Descr.«map_widen_domains/3» (D (m + 2)) tag0 (Term.list U) (boolAtom neg) = .ok r ∧
      ((neg = Bool.true ∧ (∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ r = .atom "discard") ∨
       ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ Ds then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x)) := by
  -- `lists:foldl/3` from `lists:foldl_1/3`.
  have toFoldl : ∀ res, Erlang.lists.«foldl_1/3» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res → Erlang.lists.«foldl/3» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res := fun res run => by
    cases U with
    | nil =>
      have e : res = .ok tag0 := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run.symm
      subst e
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
    | cons x xs =>
      rw [Erlang.lists.«foldl_1/3».eq_def] at run
      simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run
  rcases widen_foldP ef hm g0 gL neg Ds U [] tag0 lU fU hD g0 (fun kind _ x => by simp) with
    ⟨⟨hn, hs⟩, rr⟩ | ⟨hs, r, rr, gr, sr⟩
  · refine ⟨.atom "discard", ?_, Or.inl ⟨hn, hs, rfl⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp [Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason]
  · refine ⟨r, ?_, Or.inr ⟨hs, gr, fun kind mk x => by simpa using sr kind mk x⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp


/-- What a widened tag allows at the keys of a kind: what the tag allows, or, at the updated kinds, a value of the
type. -/
def WTagP (den : Term → V → Prop) (tag : Term) (Ds : List String) (P : String → V → Prop) (kind : String) (o : Option V) : Prop :=
  o = none ∨ ∃ x, o = some x ∧ (den (tagType tag kind) x ∨ (kind ∈ Ds ∧ P kind x))

/-- Maps of a literal whose tag is widened at some kinds. -/
def WMSemP (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (Ds : List String) (P : String → V → Prop) (w : MW V) : Prop :=
  (∀ s, FSem den tag l s (w (.atom s))) ∧ ∀ k i, WTagP den tag Ds P (domKind k) (w (.dom k i))

/-- A tag widened at kinds other than atoms holds the maps of the widened literal. -/
theorem msem_widenP (ef : EF nd E V den tl K) {tag r : Term} (g : TagV E tag) (gr : TagV E r) {Ds : List String}
    (hA : "atom" ∉ Ds) {P : String → V → Prop}
    (sr : ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
      if kind ∈ Ds then den (tagType tag kind) x ∨ P kind x else den (tagType tag kind) x)
    (l : List (Term × Term)) (w : MW V) : MSem den r l w ↔ WMSemP den tag l Ds P w := by
  have atomT : ∀ o, TagSem den r "atom" o ↔ TagSem den tag "atom" o := fun o => by
    rw [tagSem_iff ef gr, tagSem_iff ef g]
    have := sr "atom" (by simp [domainKinds])
    simp only [hA, ↓reduceIte] at this
    simp [this]
  have domT : ∀ k o, TagSem den r (domKind k) o ↔ WTagP den tag Ds P (domKind k) o := fun k o => by
    rw [tagSem_iff ef gr, WTagP]
    have := sr (domKind k) (domKind_mem k)
    by_cases dk : domKind k ∈ Ds
    · simp only [dk, ↓reduceIte, true_and] at this ⊢; simp [this]
    · simp only [dk, ↓reduceIte, false_and, or_false] at this ⊢; simp [this]
  constructor
  · intro h
    refine ⟨fun s => ?_, fun k i => (domT k _).mp (h.doms k i)⟩
    have := h.atoms s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mp this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => (domT k _).mpr (hd k i)⟩
    have := ha s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mpr this


/-- The maps a kept negation excludes after widening. -/
def NWideP (den : Term → V → Prop) (Ds : List String) (P : String → V → Prop) (N : Term) (w : MW V) : Prop :=
  ∃ (k : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer k, nt, fieldsTerm nl] ∧ WMSemP den nt nl Ds P w

/-- The fold of `map_update_widen/3` over the negations of a line: kept negations, widened, are removed. -/
theorem widen_negsP (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {tagL : Term} (gL : TagV E tagL) {P : String → V → Prop}
    (Ds : List String) (hA : "atom" ∉ Ds) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∀ (negs : List Term), (∀ N ∈ negs, MapLitV E N) → ∀ (out : Term), MField E out →
      ∃ out', Erlang.lists.«foldl/3» (D (n + 3))
          (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2 #[Term.list U]) out (Term.list negs) =
          .ok out' ∧ MField E out' ∧
        ∀ w, denMF E den out' w = Bool.true ↔ denMF E den out w = Bool.true ∧
          ∀ N ∈ negs, KeptNeg den tagL Ds N → ¬NWideP den Ds P N w := by
  intro negs lits out fo
  obtain ⟨r, ⟨o', eo, fo', so'⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-1-" #[Term.list U]
    (fun pre a => ∃ o', a = o' ∧ MField E o' ∧ ∀ w, denMF E den o' w = Bool.true ↔ denMF E den out w = Bool.true ∧
      ∀ N ∈ pre, KeptNeg den tagL Ds N → ¬NWideP den Ds P N w) negs
    (fun pre N acc mN ⟨o', ea, fo', so'⟩ => by
      subst ea
      obtain ⟨k, nt, nl, rfl, gn, snl⟩ := lits _ mN
      obtain ⟨r, rr, hr⟩ := widen_tagP ef (m := n) hn gn gL Bool.true Ds U lU fU hD
      replace rr : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 2)) nt (Term.list U) (.atom "true") = .ok r := rr
      have pureE : (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2
          #[Term.list U]) #[.tuple #[.integer k, nt, fieldsTerm nl], acc] =
          Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3» (D (n + 2)) (Term.list U)
            (.tuple #[.integer k, nt, fieldsTerm nl]) acc := by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-1-/2».pure]
      rcases hr with ⟨-, ⟨d, md, hs⟩, rfl⟩ | ⟨hs, gr, sr⟩
      · -- Discarded: unchanged.
        refine ⟨acc, ⟨acc, rfl, fo', fun w => ?_⟩, ?_⟩
        · rw [so']
          constructor
          · rintro ⟨h, hn'⟩
            refine ⟨h, fun N mN kN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN
            · simp at mN; subst mN
              obtain ⟨k', nt', nl', e, ks⟩ := kN
              obtain ⟨-, rfl, -⟩ := tuple3_inj e
              exact absurd (ks d md) hs
          · rintro ⟨h, hn'⟩; exact ⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr]
      · obtain ⟨nb, rnb, fnb, snb⟩ := map_new_leaf (den := den) ef gr snl
        obtain ⟨d', rd, fd, sd, -⟩ := map_diff_lh (den := den) fo' fnb
        refine ⟨d', ⟨d', rfl, fd, fun w => ?_⟩, ?_⟩
        · rw [sd, Bool.and_eq_true, so', Bool.not_eq_true']
          have nw : NWideP den Ds P (.tuple #[.integer k, nt, fieldsTerm nl]) w ↔ denMF E den nb w = Bool.true := by
            rw [snb, msem_widenP ef gn gr hA sr]
            constructor
            · rintro ⟨k', nt', nl', e, h⟩
              obtain ⟨-, rfl, e₃⟩ := tuple3_inj e
              rw [fieldsTerm_inj e₃]; exact h
            · intro h; exact ⟨k, nt, nl, rfl, h⟩
          constructor
          · rintro ⟨⟨h, hn'⟩, hb⟩
            refine ⟨h, fun N mN kN hN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN hN
            · simp at mN; subst mN
              rw [nw, hb] at hN; cases hN
          · rintro ⟨h, hn'⟩
            refine ⟨⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩, ?_⟩
            cases hb : denMF E den nb w
            · rfl
            · exact absurd ((nw).mpr hb) (hn' _ (by simp) ⟨k, nt, nl, rfl, hs rfl⟩)
        · rw [pureE]
          have ne : r ≠ .atom "discard" := by
            rcases gr with rfl | rfl | ⟨dl, rfl, -⟩
            · simp
            · simp
            · exact fieldsTerm_ne_atom dl "discard"
          simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr, Lynx.Except.ok_bind]
          simp [rnb, rd])
    out ⟨out, rfl, fo, fun w => by simp⟩
  subst eo
  exact ⟨r, run, fo', so'⟩


/-- The values an update puts at the keys of a kind of a line: the new type, when forcing or when the line's tag gives
the kind a value. -/
def NewP (den : Term → V → Prop) (nt : Term) (md : String) (tag : Term) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ ∃ y, den (tagType tag d) y)

/-- Kinds whose update field is not empty, at a line's tag. -/
def UpdNE (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (tag : Term) (d : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ ∃ y, den (tagType tag d) y) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- The update of one domain by `map_update_widen/3`, for any constant update: nothing when the new field is empty,
otherwise the kind, the tag's type there, and the new type. -/
theorem widen_update_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {tag : Term} (g : TagV E tag) (d : String) :
    ∃ r, Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (cOp nt nopt md) tag (.atom d) = .ok r ∧
      ((¬UpdNE den nt nopt md tag d ∧ r = .nil) ∨
        (UpdNE den nt nopt md tag d ∧ ∃ u, r = Term.list [u] ∧ DomUpdP E den tag (NewP den nt md tag) d u)) := by
  obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef hm hnt nopt hmd (old := .tuple #[tagType tag d, .atom "true"])
    ⟨_, Bool.true, rfl, tagType_value ef.mopsE g d⟩
  obtain ⟨t, o, rfl, ht⟩ := hF
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm ⟨t, o, rfl, ht⟩
  have o1 : ∀ x, FieldSem den (.tuple #[tagType tag d, .atom "true"]) (some x) ↔ den (tagType tag d) x := fun x => by
    rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
  have o0 : FieldSem den (.tuple #[tagType tag d, .atom "true"]) none := by
    rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
  have st : ∀ x, den t x ↔ NewP den nt md tag d x := fun x => by
    have := sF (some x)
    rw [fieldSem_mk, NewF] at this
    simp only [o1, o0, true_and] at this
    simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
    rw [this, NewP]
    grind
  have ne : (∃ o', NewF den nt nopt md (FieldSem den (.tuple #[tagType tag d, .atom "true"])) o') ↔
      UpdNE den nt nopt md tag d := by
    simp only [NewF, o1, o0, true_and, UpdNE]
    constructor
    · rintro ⟨o', h⟩
      grind
    · rintro (rfl | ⟨hf, hn⟩)
      · exact ⟨none, by simp⟩
      · have val : ∃ o', (o' = none ∧ nopt = Bool.true) ∨ ∃ x, o' = some x ∧ den nt x := by
          rcases hn with hn | ⟨x, hx⟩
          · exact ⟨none, Or.inl ⟨rfl, hn⟩⟩
          · exact ⟨some x, Or.inr ⟨x, rfl, hx⟩⟩
        obtain ⟨o', ho'⟩ := val
        exact ⟨o', by grind⟩
  have bI : b = Bool.true ↔ ¬UpdNE den nt nopt md tag d := by
    rw [sb, ← ne]
    simp only [sF, not_exists]
  have ev : Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (cOp nt nopt md) tag (.atom d) =
      .ok (if b = Bool.true then .nil else Term.list [.tuple #[.atom d, tagType tag d, t]]) := by
    rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
    · simp only [tagType, ↓reduceIte] at rF ⊢
      simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
      rw [rb]; cases b <;> simp [boolAtom, Term.list]
    · have tc : tagType (.atom "closed") d = .map [] := by simp [tagType]
      rw [tc] at rF ⊢
      simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
      rw [rb]; cases b <;> simp [boolAtom, Term.list]
    · have fd := find_dom d dv
      have ne := fieldsTerm_ne_atom dl
      have il := is_list_fieldsTerm dl
      have gt : Elixir.Module.Types.Descr.«fields_get/3» (fieldsTerm dl) (.atom d) (.map []) =
          .ok (tagType (fieldsTerm dl) d) := by
        rw [tagType_dom]
        simp [Elixir.Module.Types.Descr.«fields_get/3», fd]
        cases mapLookup dl (.atom d) <;> rfl
      generalize tagType (fieldsTerm dl) d = TT at gt rF ⊢
      generalize fieldsTerm dl = T at fd ne il gt
      rw [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3».eq_def]
      simp only
      split
      · exact absurd rfl (ne _)
      · exact absurd rfl (ne _)
      · simp [il, gt, rF]
        rw [rb]; cases b <;> simp [boolAtom, Term.list]
  refine ⟨_, ev, ?_⟩
  by_cases hb : b = Bool.true
  · exact Or.inl ⟨bI.mp hb, by simp [hb]⟩
  · refine Or.inr ⟨Classical.not_not.mp fun h => hb (bI.mpr h), _, by simp [hb], t, rfl, ht, st⟩

/-- The domain updates of a line, by `lists:flatmap/2` over the domains, for any constant update: the kinds whose new
field is not empty. -/
theorem widen_updates_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {tag : Term} (g : TagV E tag) :
    ∀ Ds : List String, ∃ (Ds' : List String) (U : List Term), Erlang.lists.«flatmap_1/2» (D (m + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
        (Term.list (Ds.map Term.atom)) = .ok (Term.list U) ∧ U.length = Ds'.length ∧
      (∀ p ∈ Ds'.zip U, DomUpdP E den tag (NewP den nt md tag) p.1 p.2) ∧
      ∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d
  | [] => ⟨[], [], by simp [Erlang.lists.«flatmap_1/2», Term.list], rfl, by simp, by simp⟩
  | d :: Ds => by
    obtain ⟨r, rr, hr⟩ := widen_update_gen ef hm hnt nopt hmd g d
    obtain ⟨Ds', U, rU, lU, fU, mU⟩ := widen_updates_gen ef hm hnt nopt hmd g Ds
    have step : ∀ r', (r' = [] ∨ ∃ u, r' = [u]) → r = Term.list r' → Erlang.lists.«flatmap_1/2» (D (m + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
        (Term.list ((d :: Ds).map Term.atom)) = .ok (Term.list (r' ++ U)) := fun r' hr' e => by
      subst e
      rw [Erlang.lists.«flatmap_1/2».eq_def]
      rcases hr' with rfl | ⟨u, rfl⟩
      · simp only [Term.list, List.map] at rU rr ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure, rr, rU]
      · simp only [Term.list, List.map] at rU rr ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure, rr, rU]
    rcases hr with ⟨nu, rfl⟩ | ⟨hu, u, rfl, du⟩
    · refine ⟨Ds', U, by simpa using step [] (Or.inl rfl) rfl, lU, fU, fun d' => ?_⟩
      rw [mU d']
      constructor
      · rintro ⟨m', h⟩; exact ⟨List.mem_cons_of_mem _ m', h⟩
      · rintro ⟨m', h⟩
        rcases List.mem_cons.mp m' with rfl | m'
        · exact absurd h nu
        · exact ⟨m', h⟩
    · refine ⟨d :: Ds', u :: U, by simpa using step [u] (Or.inr ⟨u, rfl⟩) rfl, by simp [lU], fun p mp => ?_, fun d' => ?_⟩
      · rcases List.mem_cons.mp mp with rfl | mp
        · exact du
        · exact fU p mp
      · rw [List.mem_cons, mU d', List.mem_cons]
        constructor
        · rintro (rfl | ⟨m', h⟩)
          · exact ⟨Or.inl rfl, hu⟩
          · exact ⟨Or.inr m', h⟩
        · rintro ⟨rfl | m', h⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨m', h⟩

theorem zip_cover {α β : Type} {A : List α} {B : List β} (h : B.length = A.length) :
    (∀ b ∈ B, ∃ a ∈ A, (a, b) ∈ A.zip B) ∧ ∀ a ∈ A, ∃ b ∈ B, (a, b) ∈ A.zip B := by
  constructor
  · intro b mb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mb
    exact ⟨A[i]'(by omega), List.getElem_mem _, List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩⟩
  · intro a ma
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ma
    exact ⟨B[i]'(by omega), List.getElem_mem _, List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩⟩

/-- The maps a line gives when widening some kinds by the values `P` gives them. -/
def WLineP (den : Term → V → Prop) (L : Term) (Ds : List String) (P : String → V → Prop) (w : MW V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    WMSemP den tag l Ds P w ∧ ∀ N ∈ negs, KeptNeg den tag Ds N → ¬NWideP den Ds P N w

/-- Whether a widened line is among the updated maps: when keeping, no kind loses the values of the line's tag and the
line does not hold the empty map; otherwise, some kind gets a value. -/
def WPres (den : Term → V → Prop) (L tag : Term) (Ds : List String) (P : String → V → Prop) (md : String) : Prop :=
  (md = "keep" → (¬∃ d ∈ Ds, (∃ y, den (tagType tag d) y) ∧ ¬∃ x, P d x) ∧ ¬InMLine den L wNone) ∧
    (md ≠ "keep" → ∃ d ∈ Ds, ∃ x, P d x)

/-- A line of `map_update_widen/3`, for any constant update. -/
theorem widen_line_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds)
    {tag : Term} {l : List (Term × Term)} {negs : List Term} (hL : MLine E (.tuple #[tag, fieldsTerm l, Term.list negs]))
    (Up Un : List Term) :
    ∃ Ds' : List String, (∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d) ∧
      ((Ds' = [] ∧ (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list Up, Term.list Un])) ∨
       (Ds' ≠ [] ∧ ∃ out, MField E out ∧ (∀ w, denMF E den out w = Bool.true ↔
          WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w) ∧
        (((D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list Up, Term.list (out :: Un)]) ∧
          (¬WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md ∨ HasReq l)) ∨
         ((D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list (out :: Up), Term.list Un]) ∧
          WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md ∧ ¬HasReq l)))) := by
  have hL' := hL
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL'
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  obtain ⟨Ds', U, rU, lU, fU, mU⟩ := widen_updates_gen ef (m := n + 3) (by omega) hnt nopt hmd g Ds
  have hD' : ∀ d ∈ Ds', d ∈ domainKinds := fun d m' => hD d ((mU d).mp m').1
  have hA' : "atom" ∉ Ds' := fun m' => hA ((mU _).mp m').1
  have pureE : ∀ a, (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
      #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs], a] =
      Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4» (D (n + 4)) (Term.list (Ds.map Term.atom))
        (cOp nt nopt md) (.tuple #[tag, fieldsTerm l, Term.list negs]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-3-/2».pure]
  have flat : Erlang.lists.«flatmap/2» (D (n + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
      (Term.list (Ds.map Term.atom)) = .ok (Term.list U) := by
    simpa [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2»] using rU
  refine ⟨Ds', mU, ?_⟩
  by_cases e0 : Ds' = []
  · subst e0
    obtain rfl : U = [] := List.eq_nil_of_length_eq_zero lU
    refine Or.inl ⟨rfl, ?_⟩
    rw [pureE]
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, Term.list, Erlang.erlang.«==/2»]
  refine Or.inr ⟨e0, ?_⟩
  obtain ⟨T, rT, hT⟩ := widen_tagP ef (m := n + 2) (by omega) g g Bool.false Ds' U lU fU hD'
  rcases hT with ⟨h, -⟩ | ⟨-, gT, sT⟩
  · cases h
  replace rT : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 4)) tag (Term.list U) (.atom "false") = .ok T := rT
  obtain ⟨b0, rb0, fb0, sb0⟩ := map_new_leaf (den := den) ef gT sl
  obtain ⟨out, rout, fout, sout⟩ := widen_negsP ef (n := n + 1) (by omega) g Ds' hA' U lU fU hD' negs lits b0 fb0
  have semOut : ∀ w, denMF E den out w = Bool.true ↔
      WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w := by
    intro w
    rw [sout, sb0, msem_widenP ef g gT hA' sT]
    constructor
    · rintro ⟨h, hn'⟩; exact ⟨tag, l, negs, rfl, h, hn'⟩
    · rintro ⟨tag', l', negs', e, h, hn'⟩
      obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
      obtain rfl := fieldsTerm_inj e₂
      obtain rfl := list_inj e₃
      exact ⟨h, hn'⟩
  -- Whether the line is among the updated maps.
  have rWP := widenPair_eval (n + 4) U fun u mu => by
    obtain ⟨d, -, mp⟩ := (zip_cover lU).1 u mu
    obtain ⟨nt', eu, -, -⟩ := fU _ mp
    exact ⟨_, _, _, eu⟩
  obtain ⟨bp, rbp, sbp⟩ := present_gen (den := den) ef (m := n + 1) (by omega) [.tuple #[tag, fieldsTerm l, Term.list negs]]
    (by simpa using hL) nt nopt hmd (U.map domPair) fun p mp => by
      obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, -, mpz⟩ := (zip_cover lU).1 u mu
      obtain ⟨nt', eu, hnt', -⟩ := fU _ mpz
      simp only at eu
      subst eu
      exact ⟨_, nt', by simp [domPair], tagType_value ef.mopsE g d, hnt'⟩
  -- The pairs are the kinds' old types and new values.
  have pairsI : ∀ (A : Prop → Prop → Prop), (∃ p ∈ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧
      A (∃ x, den o x) (∃ x, den n' x)) ↔ ∃ d ∈ Ds', A (∃ y, den (tagType tag d) y) (∃ x, NewP den nt md tag d x) := by
    intro A
    constructor
    · rintro ⟨p, mp, o, n', e, h⟩
      obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, md', mpz⟩ := (zip_cover lU).1 u mu
      obtain ⟨nt', eu, -, snt⟩ := fU _ mpz
      simp only at eu
      subst eu
      simp only [domPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [propext (exists_congr snt)] at h
      exact ⟨d, md', h⟩
    · rintro ⟨d, md', h⟩
      obtain ⟨u, mu, mpz⟩ := (zip_cover lU).2 d md'
      obtain ⟨nt', eu, -, snt⟩ := fU _ mpz
      simp only at eu
      subst eu
      rw [← propext (exists_congr snt)] at h
      exact ⟨_, List.mem_map_of_mem mu, _, nt', by simp [domPair], h⟩
  have presI : bp = Bool.true ↔
      WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md := by
    rw [sbp, WPres]
    have k1 := pairsI (fun o n => o ∧ ¬n)
    have k2 := pairsI (fun _ n => n)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun hu => (h1 hk).1 ?_, (h1 hk).2 _ (List.mem_singleton_self _)⟩, fun hk => k2.mp (h2 hk)⟩
      obtain ⟨p, mp, o, n', e, ho, hn⟩ := k1.mpr hu
      exact ⟨p, mp, o, n', e, fun x hx => hn ⟨x, hx⟩, ho⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun ⟨p, mp, o, n', e, hn, ho⟩ => (h1 hk).1 (k1.mp ⟨p, mp, o, n', e, ho, fun ⟨x, hx⟩ => hn x hx⟩),
        fun L' mL' => by simp at mL'; subst mL'; exact (h1 hk).2⟩, fun hk => k2.mpr (h2 hk)⟩
  have neU : Erlang.erlang.«==/2» (Term.list U) .nil = .ok (.atom "false") := by
    cases U with
    | nil => cases Ds' with
      | nil => exact absurd rfl e0
      | cons _ _ => simp at lU
    | cons u U' => simp [Term.list, eqq_val, boolAtom]
  refine ⟨out, fout, semOut, ?_⟩
  cases bp
  · refine Or.inl ⟨?_, Or.inl fun h => by have := presI.mpr h; cases this⟩
    rw [pureE]
    simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
      Lynx.Except.ok_bind, pure_bind]
    simp [boolAtom, Lynx.Term.isMember]
  · rcases domains_add (n + 3) out sl Up Un with ⟨ra, hr⟩ | ⟨ra, hr⟩
    · refine Or.inl ⟨?_, Or.inr hr⟩
      rw [pureE]
      simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
        Lynx.Except.ok_bind, pure_bind]
      simp [boolAtom, Lynx.Term.isMember, ra]
    · refine Or.inr ⟨?_, presI.mp rfl, hr⟩
      rw [pureE]
      simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
        Lynx.Except.ok_bind, pure_bind]
      simp [boolAtom, Lynx.Term.isMember, ra]

theorem wlineP_congr {L : Term} {A B : List String} (h : ∀ d, d ∈ A ↔ d ∈ B) {P : String → V → Prop} {w : MW V} :
    WLineP den L A P w ↔ WLineP den L B P w := by
  simp only [WLineP, WMSemP, WTagP, KeptNeg, NWideP, h]

theorem wPres_congr {L tag : Term} {A B : List String} (h : ∀ d, d ∈ A ↔ d ∈ B) {P : String → V → Prop}
    {md : String} : WPres den L tag A P md ↔ WPres den L tag B P md := by
  simp only [WPres, h]

/-- A literal with a required field holds no empty map. -/
theorem wmsemP_ne_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (hr : HasReq l) {Ds : List String}
    {P : String → V → Prop} {w : MW V} (h : WMSemP den tag l Ds P w) : w ≠ wNone := by
  rintro rfl
  obtain ⟨e, me, t, he⟩ := hr
  obtain ⟨⟨s, es⟩, -⟩ := sl.1 e me
  have := h.1 s
  unfold FSem at this
  rw [lookup_of_mem sl me es] at this
  simp only at this
  rw [he, show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at this
  simp [wNone] at this

/-- The maps `map_update_widen/3` gives from a line, for any constant update: the widened line, at the kinds whose
new field is not empty, without the empty map when the line is updated. -/
def WLG (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (Ds : List String) (L : Term) (w : MW V) :
    Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    ∃ Ds' : List String, (∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d) ∧ Ds' ≠ [] ∧
      WLineP den L Ds' (NewP den nt md tag) w ∧ (WPres den L tag Ds' (NewP den nt md tag) md → w ≠ wNone)

/-- `map_update_widen/3` for any constant update at kinds other than atoms. -/
theorem widen_run_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_widen/3» (D (n + 5)) (Term.list lines) (Term.list (Ds.map Term.atom))
        (cOp nt nopt md) = .ok (.map R) ∧ MapsD E den R (fun w => ∃ L ∈ lines, WLG den nt nopt md Ds L w) := by
  obtain ⟨r, ⟨Up, Un, rfl, fUp, fUn, sU⟩, run⟩ := foldl_rel_at (m := n + 5) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-3-" #[Term.list (Ds.map Term.atom), cOp nt nopt md]
    (fun pre a => ∃ Up Un, a = .tuple #[Term.list Up, Term.list Un] ∧ (∀ b ∈ Up, MField E b) ∧ (∀ b ∈ Un, MField E b) ∧
      ∀ w, (((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨ ∃ b ∈ Un, denMF E den b w = Bool.true) ↔
        ∃ L ∈ pre, WLG den nt nopt md Ds L w) lines
    (fun pre L a mL ⟨Up, Un, ea, fUp, fUn, sU⟩ => by
      subst ea
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      obtain ⟨Ds', mD, h⟩ := widen_line_gen ef hn hnt nopt hmd Ds hA hD (hl _ mL) Up Un
      -- The maps the new line gives.
      have wlg : ∀ w, WLG den nt nopt md Ds (.tuple #[tag, fieldsTerm l, Term.list negs]) w ↔
          Ds' ≠ [] ∧ WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w ∧
            (WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md → w ≠ wNone) := by
        intro w
        constructor
        · rintro ⟨tag', l', negs', e, Ds'', mD'', ne'', hw, hp⟩
          obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
          obtain rfl := fieldsTerm_inj e₂
          obtain rfl := list_inj e₃
          have eq : ∀ d, d ∈ Ds'' ↔ d ∈ Ds' := fun d => (mD'' d).trans (mD d).symm
          refine ⟨fun e0 => ne'' ?_, (wlineP_congr eq).mp hw, fun p => hp ((wPres_congr eq).mpr p)⟩
          cases Ds'' with
          | nil => rfl
          | cons d _ => exact absurd ((eq d).mp List.mem_cons_self) (by simp [e0])
        · rintro ⟨ne', hw, hp⟩
          exact ⟨tag, l, negs, rfl, Ds', mD, ne', hw, hp⟩
      have grow : ∀ (X : MW V → Prop), (∀ w, (((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨
          ∃ b ∈ Un, denMF E den b w = Bool.true) ↔ ∃ L ∈ pre, WLG den nt nopt md Ds L w) →
          (∀ w, X w ↔ WLG den nt nopt md Ds (.tuple #[tag, fieldsTerm l, Term.list negs]) w) →
          ∀ w, ((∃ L ∈ pre, WLG den nt nopt md Ds L w) ∨ X w) ↔
            ∃ L ∈ pre ++ [.tuple #[tag, fieldsTerm l, Term.list negs]], WLG den nt nopt md Ds L w := by
        intro X _ hX w
        rw [hX]
        constructor
        · rintro (⟨L', mL', h'⟩ | h')
          · exact ⟨L', List.mem_append_left _ mL', h'⟩
          · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h'⟩
        · rintro ⟨L', mL', h'⟩
          rcases List.mem_append.mp mL' with mL' | mL'
          · exact Or.inl ⟨L', mL', h'⟩
          · simp at mL'; subst mL'; exact Or.inr h'
      rcases h with ⟨rfl, run⟩ | ⟨ne', out, fout, sout, ⟨run, hp⟩ | ⟨run, hp, hr⟩⟩
      · refine ⟨_, ⟨Up, Un, rfl, fUp, fUn, fun w => ?_⟩, run⟩
        rw [sU w, ← grow (fun _ => False) sU (fun w => by rw [wlg]; simp) w]
        simp
      · refine ⟨_, ⟨Up, out :: Un, rfl, fUp, fun b mb => ?_, fun w => ?_⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUn b mb
        · rw [← grow (fun w => denMF E den out w = Bool.true) sU (fun w => by
            rw [wlg, sout]
            constructor
            · intro hw
              refine ⟨ne', hw, fun p => ?_⟩
              rcases hp with np | hr
              · exact absurd p np
              · obtain ⟨tag', l', negs', e, hm, -⟩ := hw
                obtain ⟨rfl, e₂, -⟩ := tuple3_inj e
                obtain rfl := fieldsTerm_inj e₂
                exact wmsemP_ne_none sl hr hm
            · rintro ⟨-, hw, -⟩; exact hw) w, ← sU w]
          simp only [List.mem_cons, exists_eq_or_imp]
          constructor
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
      · refine ⟨_, ⟨out :: Up, Un, rfl, fun b mb => ?_, fUn, fun w => ?_⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUp b mb
        · rw [← grow (fun w => denMF E den out w = Bool.true ∧ w ≠ wNone) sU (fun w => by
            rw [wlg, sout]
            constructor
            · rintro ⟨hw, nw⟩; exact ⟨ne', hw, fun _ => nw⟩
            · rintro ⟨-, hw, hn'⟩; exact ⟨hw, hn' hp⟩) w, ← sU w]
          simp only [List.mem_cons, exists_eq_or_imp]
          constructor
          · rintro (⟨h | h, nw⟩ | h)
            · exact Or.inr ⟨h, nw⟩
            · exact Or.inl (Or.inl ⟨h, nw⟩)
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h)
            · exact Or.inl ⟨Or.inr h.1, h.2⟩
            · exact Or.inr h
            · exact Or.inl ⟨Or.inl h.1, h.2⟩)
    (.tuple #[.nil, .nil]) ⟨[], [], rfl, by simp, by simp, fun w => by simp⟩
  obtain ⟨R, rR, mR⟩ := domains_result ef (m := n + 3) (by omega) Up Un fUp fUn
  refine ⟨R, ?_, mR.1, mR.2.1, fun w => (mR.2.2 w).trans (sU w)⟩
  simp [Elixir.Module.Types.Descr.«map_update_widen/3», run]
  simpa [Term.list] using rR

/-- `w` agrees with `u` off the kinds `Ds`, and at the keys of `F` of those kinds is absent, kept, or holds a value
`P` gives the kind. -/
def AgreeP (Ds : List String) (P : String → V → Prop) (F : List MKey) (w u : MW V) : Prop :=
  (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
    ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
      (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ P (domKind k) x)

theorem AgreeP.mono {Ds : List String} {P : String → V → Prop} {F G : List MKey} {w u : MW V}
    (h : AgreeP Ds P G w u) (sub : ∀ κ ∈ F, κ ∈ G) : AgreeP Ds P F w u :=
  ⟨h.1, h.2.1, fun k i m dk => h.2.2 k i (sub _ m) dk⟩

theorem wline_witnessP (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} (hA : "atom" ∉ Ds)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) {P : String → V → Prop} {w : MW V} (hw : WLineP den L Ds P w) (F : List MKey) :
    ∃ u, InMLine den L u ∧ (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
      ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
        (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ P (domKind k) x) := by
  classical
  obtain ⟨tag, l, negs, rfl, hwm, hkn⟩ := hw
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  -- What escapes a dropped negation.
  let Esc : Term → Fin 11 × V → Prop := fun N p => domKind p.1 ∈ Ds ∧ den (tagType tag (domKind p.1)) p.2 ∧
    ∀ (kN : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer kN, nt, fieldsTerm nl] →
      ¬den (tagType nt (domKind p.1)) p.2
  let pick : Term → Option (Fin 11 × V) := fun N => if h : ∃ p, Esc N p then some h.choose else none
  have exDrop : ∀ N ∈ negs, ¬KeptNeg den tag Ds N → ∃ p, Esc N p := by
    intro N mN nk
    obtain ⟨kN, nt, nl, rfl, -, -⟩ := lits N mN
    have : ¬∀ d ∈ Ds, SubAt den tag nt d := fun h => nk ⟨kN, nt, nl, rfl, h⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp this
    obtain ⟨md, hd⟩ := Classical.not_imp.mp hd
    obtain ⟨y, hy⟩ := Classical.not_forall.mp hd
    obtain ⟨hy₁, hy₂⟩ := Classical.not_imp.mp hy
    have dA : d ≠ "atom" := fun h => hA (h ▸ md)
    obtain ⟨k, rfl⟩ := domKind_of (hD _ md) dA
    refine ⟨(k, y), md, hy₁, fun kN' nt' nl' e' => ?_⟩
    obtain ⟨-, rfl, -⟩ := tuple3_inj e'
    exact hy₂
  let J := freshIdx F
  let isOld : Fin 11 → Option V → Prop := fun k o => ∃ x, o = some x ∧ den (tagType tag (domKind k)) x
  let u : MW V := fun κ => match κ with
    | .atom s => w (.atom s)
    | .dom k i => if domKind k ∈ Ds then
        (if MKey.dom k i ∈ F then (if isOld k (w (.dom k i)) then w (.dom k i) else none)
         else if J ≤ i then (match negs[i - J]? with
             | some N => (match pick N with | some p => if p.1 = k then some p.2 else none | none => none)
             | none => none)
         else none)
      else w (.dom k i)
  have pickOk : ∀ N p, pick N = some p → Esc N p := by
    intro N p hp
    simp only [pick] at hp
    split at hp
    · rename_i h; cases hp; exact h.choose_spec
    · cases hp
  have uA : ∀ s, u (.atom s) = w (.atom s) := fun s => rfl
  have uN : ∀ k i, domKind k ∉ Ds → u (.dom k i) = w (.dom k i) := fun k i h => by simp [u, h]
  have uF : ∀ k i, MKey.dom k i ∈ F → domKind k ∈ Ds →
      u (.dom k i) = if isOld k (w (.dom k i)) then w (.dom k i) else none := fun k i m h => by simp [u, h, m]
  -- Every value of the witness at a domain key is allowed by the tag.
  have allowed : ∀ k i, TagSem den tag (domKind k) (u (.dom k i)) := by
    intro k i
    rw [tagSem_iff ef g]
    by_cases dk : domKind k ∈ Ds
    · by_cases mF : MKey.dom k i ∈ F
      · rw [uF k i mF dk]
        split
        · rename_i h; obtain ⟨x, e, hx⟩ := h; exact Or.inr ⟨x, e, hx⟩
        · exact Or.inl rfl
      · simp only [u, dk, ↓reduceIte, mF]
        split
        · cases hN : negs[i - J]? with
          | none => exact Or.inl rfl
          | some N =>
            simp only
            cases hp : pick N with
            | none => exact Or.inl rfl
            | some p =>
              simp only
              by_cases e : p.1 = k
              · obtain ⟨-, hy, -⟩ := pickOk N p hp
                rw [e] at hy
                simp only [e, ↓reduceIte]
                exact Or.inr ⟨_, rfl, hy⟩
              · simp [e]
        · exact Or.inl rfl
    · rw [uN k i dk]
      rcases hwm.2 k i with h | ⟨x, e, h | ⟨h, -⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, e, h⟩
      · exact absurd h dk
  refine ⟨u, ⟨tag, l, negs, rfl, ⟨fun s => by rw [uA]; exact hwm.1 s, allowed⟩, fun N mN hN => ?_⟩, fun s => (uA s).symm,
    fun k i h => (uN k i h).symm, fun k i mF dk => ?_⟩
  · obtain ⟨kN, nt, nl, rfl, gN, slN⟩ := lits N mN
    obtain ⟨kN', nt', nl', e', hm⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    by_cases kept : KeptNeg den tag Ds (.tuple #[.integer kN, nt, fieldsTerm nl])
    · -- A kept negation already excludes the line's maps on their non-updated part.
      refine hkn _ mN kept ⟨kN, nt, nl, rfl, fun s => by rw [← uA]; exact hm.atoms s, fun k i => ?_⟩
      obtain ⟨kN'', nt'', nl'', e'', sub⟩ := kept
      obtain ⟨-, rfl, -⟩ := tuple3_inj e''
      by_cases dk : domKind k ∈ Ds
      · rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl (sub _ dk x h)⟩
        · exact Or.inr ⟨x, e, Or.inr ⟨dk, h⟩⟩
      · have := hm.doms k i
        rw [uN k i dk, tagSem_iff ef gN] at this
        rcases this with h | ⟨x, e, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl h⟩
    · -- A dropped negation misses the fresh key holding its escape value.
      obtain ⟨p, hp⟩ := exDrop _ mN kept
      have hpick : ∃ q, pick (.tuple #[.integer kN, nt, fieldsTerm nl]) = some q :=
        ⟨_, by simp only [pick, show ∃ p, Esc (.tuple #[.integer kN, nt, fieldsTerm nl]) p from ⟨p, hp⟩, ↓reduceDIte]; rfl⟩
      obtain ⟨q, hq⟩ := hpick
      obtain ⟨dq, -, nq⟩ := pickOk _ q hq
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp mN
      have fresh : MKey.dom q.1 (J + idx) ∉ F := freshIdx_not_mem (by omega)
      have uq : u (.dom q.1 (J + idx)) = some q.2 := by
        simp [u, dq, fresh, hidx, hq]
      have := hm.doms q.1 (J + idx)
      rw [uq, tagSem_iff ef gN] at this
      rcases this with h | ⟨x, e, h⟩
      · cases h
      · cases e; exact nq kN nt nl rfl h
  · rw [uF k i mF dk]
    rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
    · exact Or.inl h
    · right; left
      simp only [show isOld k (w (.dom k i)) from ⟨x, e, h⟩, ↓reduceIte]
    · exact Or.inr (Or.inr ⟨x, e, h⟩)


/-- A map agreeing, on every finite set of keys, with some map of a line is a map of the widened line. -/
theorem wline_of_agreeP (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} {P : String → V → Prop} {w : MW V}
    (h : ∀ F, ∃ u, InMLine den L u ∧ AgreeP Ds P F w u) : WLineP den L Ds P w := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨u₀, hu₀, a₀⟩ := h []
  obtain ⟨m₀, n₀⟩ := inMLine_iff.mp hu₀
  refine ⟨tag, l, negs, rfl, ⟨fun s => by rw [a₀.1 s]; exact m₀.atoms s, fun k i => ?_⟩, fun N mN kept hN => ?_⟩
  · obtain ⟨u, hu, a⟩ := h [.dom k i]
    have t := (inMLine_iff.mp hu).1.doms k i
    rw [tagSem_iff ef g] at t
    by_cases dk : domKind k ∈ Ds
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx⟩
      · exact Or.inl e
      · rw [e]
        rcases t with t | ⟨x, t, hx⟩
        · exact Or.inl t
        · exact Or.inr ⟨x, t, Or.inl hx⟩
      · exact Or.inr ⟨x, e, Or.inr ⟨dk, hx⟩⟩
    · rw [a.2.1 k i dk]
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, Or.inl hx⟩
  · -- `u₀` would be a map of the kept negation.
    obtain ⟨kN, nt, nl, rfl, sub⟩ := kept
    obtain ⟨kN', nt', nl', e', hw⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    obtain ⟨kN'', nt'', nl'', e'', gN, -⟩ := lits _ mN
    obtain ⟨-, rfl, -⟩ := tuple3_inj e''
    refine n₀ _ mN ⟨kN, nt, nl, rfl, fun s => by rw [← a₀.1 s]; exact hw.1 s, fun k i => ?_⟩
    rw [tagSem_iff ef gN]
    by_cases dk : domKind k ∈ Ds
    · have t := m₀.doms k i
      rw [tagSem_iff ef g] at t
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, sub _ dk x hx⟩
    · rw [← a₀.2.1 k i dk]
      rcases hw.2 k i with t | ⟨x, t, hx | ⟨hd, _⟩⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, hx⟩
      · exact absurd hd dk


/-- A map holds a key of a kind. -/
def HasKind (u : MW V) (d : String) : Prop := ∃ k i, domKind k = d ∧ u (.dom k i) ≠ none

/-- A value of a map of a line at a key of a kind is a value of the line's tag there. -/
theorem inline_tag (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u) {k : Fin 11}
    {i : Nat} {x : V} (e : u (.dom k i) = some x) : den (tagType tag (domKind k)) x := by
  have t := (inMLine_iff.mp hu).1.doms k i
  rw [tagSem_iff ef g, e] at t
  rcases t with t | ⟨y, t, hy⟩
  · cases t
  · cases t; exact hy

theorem inline_hasKind (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u) {d : String}
    (h : HasKind u d) : ∃ y, den (tagType tag d) y := by
  obtain ⟨k, i, rfl, ne⟩ := h
  cases e : u (.dom k i) with
  | none => exact absurd e ne
  | some x => exact ⟨x, inline_tag ef g hu e⟩

/-- A map of a line gives one holding a key of each kind the tag gives a value, agreeing elsewhere and on a finite
set of keys. -/
theorem line_extend (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u)
    (SK : Fin 11 → Prop) (hS : ∀ k, SK k → ∃ y, den (tagType tag (domKind k)) y) (F : List MKey) :
    ∃ u', InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u' ∧ (∀ s, u' (.atom s) = u (.atom s)) ∧
      (∀ κ ∈ F, u' κ = u κ) ∧ (∀ k i, ¬SK k → u' (.dom k i) = u (.dom k i)) ∧ ∀ k, SK k → ∃ i, u' (.dom k i) ≠ none := by
  classical
  let J := freshIdx F
  let u' : MW V := fun κ => match κ with
    | .atom s => u (.atom s)
    | .dom k i => if h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J then some (hS k h.1).choose else u (.dom k i)
  have uD : ∀ k i, ¬(SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J) → u' (.dom k i) = u (.dom k i) := fun k i h => by
    simp only [u']; rw [dite_eq_right h]
  have uS : ∀ k i (h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J), u' (.dom k i) = some (hS k h.1).choose :=
    fun k i h => by simp only [u']; rw [dite_eq_left h]
  obtain ⟨m, nn⟩ := inMLine_iff.mp hu
  refine ⟨u', inMLine_iff.mpr ⟨⟨fun s => m.atoms s, fun k i => ?_⟩, fun N mN hN => ?_⟩, fun s => rfl,
    fun κ mκ => ?_, fun k i nk => uD k i (fun h => nk h.1), fun k sk => ?_⟩
  · by_cases h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J
    · rw [uS k i h, tagSem_iff ef g]; exact Or.inr ⟨_, rfl, (hS k h.1).choose_spec⟩
    · rw [uD k i h]; exact m.doms k i
  · obtain ⟨kN, tN, lN, rfl, hm⟩ := hN
    refine nn _ mN ⟨kN, tN, lN, rfl, ⟨fun s => hm.atoms s, fun k i => ?_⟩⟩
    by_cases h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J
    · rw [h.2.1 i]; exact tagSem_none _ _
    · rw [← uD k i h]; exact hm.doms k i
  · cases κ with
    | atom s => rfl
    | dom k i => exact uD k i fun h => freshIdx_not_mem (k := k) (Nat.le_of_eq h.2.2.symm) mκ
  · by_cases ex : ∃ i, u (.dom k i) ≠ none
    · obtain ⟨i, hi⟩ := ex
      refine ⟨i, ?_⟩
      rw [uD k i fun h => hi (h.2.1 i)]; exact hi
    · have h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ J = J :=
        ⟨sk, fun i' => Classical.not_not.mp fun hh => ex ⟨i', hh⟩, rfl⟩
      exact ⟨J, by rw [uS k J h]; simp⟩

/-- The maps of a line are maps of the widened line. -/
theorem inline_wline (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String}
    {P : String → V → Prop} {u : MW V} (hu : InMLine den L u) : WLineP den L Ds P u :=
  wline_of_agreeP ef hL fun _ => ⟨u, hu, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => Or.inr (Or.inl rfl)⟩

/-- A line whose tag gives no value at the widened kinds, widened by no value, is the line. -/
theorem wline_static (ef : EF nd E V den tl K) {tag : Term} {l : List (Term × Term)} {negs : List Term}
    (hL : MLine E (.tuple #[tag, fieldsTerm l, Term.list negs])) {Ds : List String}
    (hT : ∀ d ∈ Ds, ∀ y, ¬den (tagType tag d) y) {P : String → V → Prop} (hP : ∀ d ∈ Ds, ∀ x, ¬P d x) {w : MW V}
    (hw : WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds P w) :
    InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w := by
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  obtain ⟨tag', l', negs', e, hm, hn⟩ := hw
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  refine inMLine_iff.mpr ⟨⟨hm.1, fun k i => ?_⟩, fun N mN hN => ?_⟩
  · rw [tagSem_iff ef g]
    rcases hm.2 k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, hx⟩
    · exact absurd hx (hP _ dk x)
  · obtain ⟨kN, tN, lN, rfl, gN, -⟩ := lits N mN
    obtain ⟨kN', tN', lN', e', hm'⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    refine hn _ mN ⟨kN, tN, lN, rfl, fun d md y hy => absurd hy (hT d md y)⟩
      ⟨kN, tN, lN, rfl, fun s => hm'.atoms s, fun k i => ?_⟩
    have := hm'.doms k i
    rw [tagSem_iff ef gN] at this
    rcases this with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, Or.inl hx⟩

/-- On finitely many lines, a property every finite set of keys meets on some line, antitone in the set, holds for
every finite set on one line. -/
theorem pigeon_lines {lines : List Term} {Q : Term → List MKey → Prop}
    (mono : ∀ L F G, Q L G → (∀ κ ∈ F, κ ∈ G) → Q L F) (h : ∀ F, ∃ L ∈ lines, Q L F) :
    ∃ L ∈ lines, ∀ F, Q L F := by
  classical
  let FL : Term → List MKey := fun L => if hr : ∃ F, ¬Q L F then hr.choose else []
  obtain ⟨L, mL, hq⟩ := h (lines.flatMap FL)
  refine ⟨L, mL, Classical.byContradiction fun nq => ?_⟩
  have hr : ∃ F, ¬Q L F := Classical.not_forall.mp nq
  have hF : FL L = hr.choose := by simp only [FL, hr, ↓reduceDIte]
  exact hr.choose_spec (mono L _ _ hq fun κ m => List.mem_flatMap.mpr ⟨L, mL, hF ▸ m⟩)

/-- The values an update may put at the keys of a kind of a map: the new type, when forcing or when the map holds a
key of the kind. -/
def NewU (den : Term → V → Prop) (nt : Term) (md : String) (u : MW V) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ HasKind u d)

/-- The maps `map_update_widen/3` gives for a constant update, from the maps of a type: on every finite set of keys,
some map of the type, holding a key of an updated kind when rejecting, agrees as `AgreeP` requires. -/
def WSem (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (Ds : List String) (w : MW V) : Prop :=
  ∀ F, ∃ u, M u ∧ (md = "reject" → ∃ d ∈ Ds, HasKind u d) ∧ AgreeP Ds (NewU den nt md u) F w u

/-- `WSem` without the empty map when keys get values, unless keeping and the type holds it. -/
def WRes (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (Ds : List String) (w : MW V) : Prop :=
  WSem den M nt md Ds w ∧ ((∃ x, den nt x) → (md = "keep" → w = wNone → M wNone) ∧ (md ≠ "keep" → w ≠ wNone))

theorem updNE_iff {nt : Term} {nopt : Bool} (hne : nopt = Bool.true ∨ ∃ x, den nt x) {md : String} (hmd : Mode md)
    {tag : Term} {d : String} : UpdNE den nt nopt md tag d ↔ (md = "reject" → ∃ y, den (tagType tag d) y) := by
  unfold UpdNE
  rcases hmd with rfl | rfl | rfl
  · simp [hne]
  · simp
  · simp [hne]

/-- The widened lines of a type hold the maps `WRes` describes. -/
theorem wlg_sem (ef : EF nd E V den tl K) {lines : List Term} (hl : ∀ L ∈ lines, MLine E L) {nt : Term} (nopt : Bool)
    (hne : nopt = Bool.true ∨ ∃ x, den nt x) {md : String} (hmd : Mode md) {Ds : List String} (hA : "atom" ∉ Ds)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) (neD : Ds ≠ []) (w : MW V) :
    (∃ L ∈ lines, WLG den nt nopt md Ds L w) ↔ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) nt md Ds w := by
  classical
  constructor
  · rintro ⟨L, mL, tag, l, negs, rfl, Ds', mD, ne', hw, hp⟩
    obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hl _ mL
    obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
    obtain rfl := fieldsTerm_inj e₂
    obtain rfl := list_inj e₃
    have hD' : ∀ d ∈ Ds', d ∈ domainKinds := fun d m' => hD d ((mD d).mp m').1
    have hA' : "atom" ∉ Ds' := fun m' => hA ((mD _).mp m').1
    refine ⟨fun F => ?_, fun hnt => ⟨?_, ?_⟩⟩
    · obtain ⟨u, hu, a1, a2, a3⟩ := wline_witnessP ef (hl _ mL) hA' hD' hw F
      obtain ⟨u', hu', b1, bF, bS, bK⟩ := line_extend ef g hu
        (fun k => domKind k ∈ Ds' ∧ ∃ y, den (tagType tag (domKind k)) y) (fun _ h => h.2) F
      refine ⟨u', ⟨_, mL, hu'⟩, fun hr => ?_, fun s => (a1 s).trans (b1 s).symm, fun k i nk => ?_,
        fun k i mF dk => ?_⟩
      · obtain ⟨d, md'⟩ := List.exists_mem_of_ne_nil Ds' ne'
        obtain ⟨dD, up⟩ := (mD d).mp md'
        have tne := (updNE_iff hne hmd).mp up hr
        obtain ⟨k, rfl⟩ := domKind_of (hD _ dD) (fun h => hA (h ▸ dD))
        obtain ⟨i, hi⟩ := bK k ⟨md', tne⟩
        exact ⟨_, dD, k, i, rfl, hi⟩
      · have nk' : domKind k ∉ Ds' := fun m' => nk ((mD _).mp m').1
        rw [a2 k i nk', bS k i (fun h => nk' h.1)]
      · by_cases dk' : domKind k ∈ Ds'
        · rcases a3 k i mF dk' with h | h | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl (h.trans (bF _ mF).symm))
          · refine Or.inr (Or.inr ⟨x, h, hx.1, ?_⟩)
            rcases hx.2 with hf | tne
            · exact Or.inl hf
            · obtain ⟨i', hi'⟩ := bK k ⟨dk', tne⟩
              exact Or.inr ⟨k, i', rfl, hi'⟩
        · exact Or.inr (Or.inl ((a2 k i dk').trans (bF _ mF).symm))
    · rintro rfl rfl
      by_cases inL : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone
      · exact ⟨_, mL, inL⟩
      obtain ⟨x, hx⟩ := hnt
      exact absurd rfl (hp ⟨fun _ => ⟨fun ⟨d, md', ⟨y, hy⟩, hn⟩ => hn ⟨x, hx, Or.inr ⟨y, hy⟩⟩, inL⟩,
        fun hk => absurd rfl hk⟩)
    · intro nk
      obtain ⟨d, md'⟩ := List.exists_mem_of_ne_nil Ds' ne'
      obtain ⟨x, hx⟩ := hnt
      refine hp ⟨fun hk => absurd hk nk, fun _ => ⟨d, md', x, hx, ?_⟩⟩
      rcases hmd with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl nk
      · exact Or.inr ((updNE_iff hne (Or.inr (Or.inr rfl))).mp ((mD d).mp md').2 rfl)
  · rintro ⟨hs, he⟩
    by_cases special : md = "keep" ∧ (∃ x, den nt x) ∧ w = wNone
    · obtain ⟨rfl, hnt, rfl⟩ := special
      obtain ⟨L, mL, hL⟩ := (he hnt).1 rfl rfl
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      exact ⟨_, mL, tag, l, negs, rfl, Ds, fun d => ⟨fun m' => ⟨m', Or.inl rfl⟩, fun h => h.1⟩, neD,
        inline_wline ef (hl _ mL) hL, fun p => absurd hL (p.1 rfl).2⟩
    obtain ⟨L, mL, hQ⟩ := pigeon_lines (lines := lines)
      (Q := fun L F => ∃ u, InMLine den L u ∧ (md = "reject" → ∃ d ∈ Ds, HasKind u d) ∧
        AgreeP Ds (NewU den nt md u) F w u)
      (fun L F G ⟨u, hu, hr, a⟩ sub => ⟨u, hu, hr, a.mono sub⟩)
      (fun F => by
        obtain ⟨u, ⟨L, mL, hu⟩, hr, a⟩ := hs F
        exact ⟨L, mL, u, hu, hr, a⟩)
    obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
    let Ds' := Ds.filter (fun d => decide (UpdNE den nt nopt md tag d))
    have mD : ∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d := fun d => by simp [Ds']
    have hk : ∀ d, d ∈ Ds → d ∉ Ds' → md = "reject" ∧ ∀ y, ¬den (tagType tag d) y := fun d dD nD => by
      have : ¬UpdNE den nt nopt md tag d := fun h => nD ((mD d).mpr ⟨dD, h⟩)
      rw [updNE_iff hne hmd] at this
      obtain ⟨hr, hy⟩ := Classical.not_imp.mp this
      exact ⟨hr, fun y h => hy ⟨y, h⟩⟩
    have noKey : ∀ k i, domKind k ∈ Ds → domKind k ∉ Ds' → w (.dom k i) = none ∧
        ∀ u, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u → u (.dom k i) = none := by
      intro k i dD nD
      obtain ⟨hr, hy⟩ := hk _ dD nD
      have uN : ∀ u, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u → u (.dom k i) = none := by
        intro u hu
        cases e : u (.dom k i) with
        | none => rfl
        | some x => exact absurd (inline_tag ef g hu e) (hy x)
      refine ⟨?_, uN⟩
      obtain ⟨u, hu, -, a⟩ := hQ [.dom k i]
      rcases a.2.2 k i (List.mem_singleton_self _) dD with h | h | ⟨x, h, hx⟩
      · exact h
      · exact h.trans (uN u hu)
      · rcases hx.2 with hf | hK
        · rw [hr] at hf; simp at hf
        · obtain ⟨y, hy'⟩ := inline_hasKind ef g hu hK
          exact absurd hy' (hy y)
    have ne' : Ds' ≠ [] := by
      by_cases hr : md = "reject"
      · obtain ⟨u, hu, hk', -⟩ := hQ []
        obtain ⟨d, dD, hK⟩ := hk' hr
        have := inline_hasKind ef g hu hK
        intro e
        have m' := (mD d).mpr ⟨dD, (updNE_iff hne hmd).mpr fun _ => this⟩
        rw [e] at m'; cases m'
      · obtain ⟨d, dD⟩ := List.exists_mem_of_ne_nil Ds neD
        intro e
        have m' := (mD d).mpr ⟨dD, (updNE_iff hne hmd).mpr fun h => absurd h hr⟩
        rw [e] at m'; cases m'
    have hw : WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w :=
      wline_of_agreeP ef (hl _ mL) fun F => by
        obtain ⟨u, hu, -, a⟩ := hQ F
        refine ⟨u, hu, a.1, fun k i nD => ?_, fun k i mF dk => ?_⟩
        · by_cases dD : domKind k ∈ Ds
          · obtain ⟨hw, hu'⟩ := noKey k i dD nD
            rw [hw, hu' u hu]
          · exact a.2.1 k i dD
        · rcases a.2.2 k i mF ((mD _).mp dk).1 with h | h | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · refine Or.inr (Or.inr ⟨x, h, hx.1, ?_⟩)
            rcases hx.2 with hf | hK
            · exact Or.inl hf
            · exact Or.inr (inline_hasKind ef g hu hK)
    refine ⟨_, mL, tag, l, negs, rfl, Ds', mD, ne', hw, fun p => ?_⟩
    rintro rfl
    by_cases mk : md = "keep"
    · subst mk
      by_cases hnt : ∃ x, den nt x
      · exact special ⟨rfl, hnt, rfl⟩
      · -- Deleting: no kind gets a value, so every updated kind lacks values and the line is unchanged.
        have tE : ∀ d ∈ Ds', ∀ y, ¬den (tagType tag d) y := fun d md' y hy =>
          (p.1 rfl).1 ⟨d, md', ⟨y, hy⟩, fun ⟨x, hx⟩ => hnt ⟨x, hx.1⟩⟩
        exact (p.1 rfl).2 (wline_static ef (hl _ mL) tE (fun d _ x hx => hnt ⟨x, hx.1⟩) hw)
    · obtain ⟨d, -, x, hx, -⟩ := p.2 mk
      exact (he ⟨x, hx⟩).2 mk rfl

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! The maps of `map_update_box/6`, described from the maps of a type rather than its lines. -/

/-- The maps hold atom keys outside every finite set. -/
def AtomsInf (M : MW V → Prop) : Prop := ∀ F : List String, ∃ u, M u ∧ ∃ s, s ∉ F ∧ u (.atom s) ≠ none

/-- The maps hold keys of a kind: atoms outside every finite set, or keys of another kind. -/
def KindHeld (M : MW V → Prop) (d : String) : Prop :=
  (d = "atom" → AtomsInf M) ∧ (d ≠ "atom" → ∃ u, M u ∧ HasKind u d)

/-- A value the maps hold at a key of a kind other than atoms. -/
def KindVal (M : MW V → Prop) (d : String) (x : V) : Prop := ∃ u k j, M u ∧ domKind k = d ∧ u (.dom k j) = some x

/-- The values an update puts at the keys of a kind. -/
def NewDomS (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ KindHeld M d)

/-- Kinds whose update field is not empty. -/
def DomNES (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (nopt : Bool) (md : String) (d : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ KindHeld M d) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- Atom keys of the key type whose update field is not empty. -/
def KeyNES (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (s : String) : Prop :=
  s ∉ S ∧ ∃ o, NewF den nt nopt md (Old M (.atom s)) o

/-- Some updated key or kind of the key type has old values or new values as `A` asks. -/
def UpdHasS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (A : Prop → Prop → Prop) : Prop :=
  (∃ s, KeyNES den M S nt nopt md s ∧ A (∃ x, Old M (.atom s) (some x))
      (∃ x, NewF den nt nopt md (Old M (.atom s)) (some x))) ∨
    ∃ d ∈ Ds, d ≠ "atom" ∧ DomNES den M nt nopt md d ∧ A (∃ x, KindVal M d x) (∃ x, NewDomS den M nt md d x)

/-- Rejecting with a single key of the key type held and no other kind: that key is replaced. -/
def RS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (s : String) : Prop :=
  md = "reject" ∧ (∀ d ∈ Ds, d ≠ "atom" → ¬DomNES den M nt nopt md d) ∧ KeyNES den M S nt nopt md s ∧
    ∀ s', KeyNES den M S nt nopt md s' → s' = s

/-- The box: every key holds an old value, or, in the key type, a new one. -/
def SynS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (w : MW V) : Prop :=
  (∀ s, (s ∈ S ∧ Old M (.atom s) (w (.atom s))) ∨ (s ∉ S ∧ ((¬RS den M S nt nopt md Ds s ∧ Old M (.atom s) (w (.atom s))) ∨
      NewF den nt nopt md (Old M (.atom s)) (w (.atom s))))) ∧
    ∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧
      (KindVal M (domKind k) x ∨ (domKind k ∈ Ds ∧ NewDomS den M nt md (domKind k) x))

/-- No key of the key type holds a new value. -/
def UnsetS (den : Term → V → Prop) (S : List String) (Ds : List String) (nt : Term) (w : MW V) : Prop :=
  (∀ s, s ∉ S → OutV den nt (w (.atom s))) ∧ ∀ k i, domKind k ∈ Ds → OutV den nt (w (.dom k i))

/-- Whether the box is among the updated maps. -/
def PresentS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) : Prop :=
  (md = "keep" → ¬UpdHasS den M S nt nopt md Ds (fun o n => o ∧ ¬n) ∧ ¬M wNone) ∧
    (md ≠ "keep" → UpdHasS den M S nt nopt md Ds (fun _ n => n))

/-- Keeping absent keys, with no key of the key type holding old or new values. -/
def SameS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) : Prop :=
  md = "keep" ∧ ¬UpdHasS den M S nt nopt md Ds (fun o n => o ∨ n)

/-- The maps of `map_update_box/6`, from the maps of a type, the atoms outside the key type, and the kinds updated. -/
def BoxSem (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (w : MW V) : Prop :=
  UpdHasS den M S nt nopt md Ds (fun _ _ => True) ∧ (SameS den M S nt nopt md Ds → M w) ∧
    (¬SameS den M S nt nopt md Ds → SynS den M S nt nopt md Ds w ∧
      (PresentS den M S nt nopt md Ds →
        ((nopt = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds) → ¬UnsetS den S Ds nt w) ∧
        (¬(nopt = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds) → w ≠ wNone)))

/-- The new field of a key some map lacks, holding a value. -/
theorem newF_some {nt : Term} {nopt : Bool} {md : String} {Old : Option V → Prop} (h0 : Old none) (x : V) :
    NewF den nt nopt md Old (some x) ↔ den nt x ∧ (md = "force" ∨ ∃ y, Old (some y)) := by
  unfold NewF
  constructor
  · rintro (⟨ho, (⟨h, -⟩ | ⟨z, h, hz⟩)⟩ | ⟨-, (⟨rfl, (⟨h, -⟩ | ⟨z, h, hz⟩)⟩ | ⟨-, h⟩)⟩)
    · cases h
    · cases h; exact ⟨hz, Or.inr ho⟩
    · cases h
    · cases h; exact ⟨hz, Or.inl rfl⟩
    · cases h
  · rintro ⟨hx, rfl | ho⟩
    · exact Or.inr ⟨h0, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx⟩⟩⟩
    · exact Or.inl ⟨ho, Or.inr ⟨x, rfl, hx⟩⟩

/-- Whether the new field of a key some map lacks is not empty. -/
theorem newF_ex {nt : Term} {nopt : Bool} {md : String} {Old : Option V → Prop} (h0 : Old none) :
    (∃ o, NewF den nt nopt md Old o) ↔
      md = "keep" ∨ ((md = "force" ∨ ∃ y, Old (some y)) ∧ (nopt = Bool.true ∨ ∃ x, den nt x)) := by
  unfold NewF
  constructor
  · rintro ⟨o, (⟨ho, (⟨-, hn⟩ | ⟨z, -, hz⟩)⟩ | ⟨-, (⟨rfl, (⟨-, hn⟩ | ⟨z, -, hz⟩)⟩ | ⟨hk, -⟩)⟩)⟩
    · exact Or.inr ⟨Or.inr ho, Or.inl hn⟩
    · exact Or.inr ⟨Or.inr ho, Or.inr ⟨z, hz⟩⟩
    · exact Or.inr ⟨Or.inl rfl, Or.inl hn⟩
    · exact Or.inr ⟨Or.inl rfl, Or.inr ⟨z, hz⟩⟩
    · exact Or.inl hk
  · rintro (hk | ⟨hf, hn⟩)
    · exact ⟨none, Or.inr ⟨h0, Or.inr ⟨hk, rfl⟩⟩⟩
    · have val : ∃ o, (o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x := by
        rcases hn with hn | ⟨x, hx⟩
        · exact ⟨none, Or.inl ⟨rfl, hn⟩⟩
        · exact ⟨some x, Or.inr ⟨x, rfl, hx⟩⟩
      obtain ⟨o, ho⟩ := val
      rcases hf with rfl | hy
      · exact ⟨o, Or.inr ⟨h0, Or.inl ⟨rfl, ho⟩⟩⟩
      · exact ⟨o, Or.inl ⟨hy, ho⟩⟩

section lines
variable (ef : EF nd E V den tl K) {lines : List Term} (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
include ef hl

/-- Atoms no line names hold absence or what the tags of the lines allow at atoms. -/
theorem unnamed_old (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK)
    {s : String} (ns : s ∉ NK) (o : Option V) :
    Old (fun u => ∃ L ∈ lines, InMLine den L u) (.atom s) o ↔
      o = none ∨ ∃ x, o = some x ∧ ∃ L ∈ lines, LineTag den L "atom" x := by
  have notIn : ∀ L ∈ lines, ¬LineNames L s := fun L mL h => ns (lnNK L mL s h)
  constructor
  · rintro ⟨u, ⟨L, mL, hu⟩, rfl⟩
    cases ho : u (.atom s) with
    | none => exact Or.inl rfl
    | some x =>
      refine Or.inr ⟨x, rfl, L, mL, ?_⟩
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
      have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
      have := (inMLine_iff.mp hu).1.atoms s
      simp only [FSem, lookup_fresh' sl, ho] at this
      exact ⟨tag, l, negs, rfl, (tagSem_some ef g "atom" x).mp this⟩
  · intro h
    obtain ⟨L, mL, hx⟩ : ∃ L ∈ lines, (o = none ∨ ∃ x, o = some x ∧ LineTag den L "atom" x) := by
      rcases h with rfl | ⟨x, rfl, L, mL, hL⟩
      · obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
        exact ⟨L, mL, Or.inl rfl⟩
      · exact ⟨L, mL, Or.inr ⟨x, rfl, hL⟩⟩
    obtain ⟨⟨tag, l, negs, rfl, g, -, lits⟩, w₀, h₀⟩ := hl L mL
    have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
    have sn : s ∉ negStrs negs := fun m => by
      obtain ⟨N, mN, ms⟩ := List.mem_flatMap.mp m
      obtain ⟨k, t, l', rfl, -, -⟩ := lits N mN
      simp only [litStrs, domFields_fieldsTerm] at ms
      exact notIn _ mL ⟨tag, l, negs, rfl, Or.inr ⟨_, mN, k, t, l', rfl, ms⟩⟩
    have ho : TagSem den tag "atom" o := by
      rcases hx with rfl | ⟨x, rfl, tag', l', negs', e, hx⟩
      · exact tagSem_none tag "atom"
      · obtain ⟨rfl, -, -⟩ := tuple3_inj e
        exact (tagSem_some ef g "atom" x).mpr hx
    obtain ⟨u, hu, e⟩ := line_at h₀ lits sl sn ho
    exact ⟨u, ⟨_, mL, hu⟩, e⟩

/-- Keys of kinds other than atoms hold what the tags of the lines allow at their kind. -/
theorem dom_val (k : Fin 11) (x : V) :
    (∃ L ∈ lines, LineTag den L (domKind k) x) ↔ KindVal (fun u => ∃ L ∈ lines, InMLine den L u) (domKind k) x := by
  constructor
  · rintro ⟨L, mL, hx⟩
    obtain ⟨u, hu, κ, hκ, e⟩ := tag_witness ef (hl L mL).1 (hl L mL).2 (domKind_mem k) hx []
    rcases hκ with ⟨h, -⟩ | ⟨k', j, ek, rfl⟩
    · exact absurd h (domKind_ne_atom k)
    · exact ⟨u, k', j, ⟨L, mL, hu⟩, ek.symm, e⟩
  · rintro ⟨u, k', j, ⟨L, mL, hu⟩, ek, e⟩
    obtain rfl : k' = k := domKind_inj ek
    obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
    have := (inMLine_iff.mp hu).1.doms k' j
    rw [e] at this
    exact ⟨_, mL, tag, l, negs, rfl, (tagSem_some ef g _ x).mp this⟩

/-- The kinds other than atoms whose keys the maps hold are those some line's tag allows. -/
theorem kind_held_ne {d : String} (hd : d ∈ domainKinds) (da : d ≠ "atom") :
    KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
  obtain ⟨k, rfl⟩ := domKind_of hd da
  constructor
  · intro h
    obtain ⟨u, hu, k', i, ek, hi⟩ := h.2 da
    cases e : u (.dom k' i) with
    | none => exact absurd e hi
    | some x =>
      obtain rfl : k' = k := domKind_inj ek
      obtain ⟨L, mL, hL⟩ := (dom_val ef hl k' x).mpr ⟨u, k', i, hu, rfl, e⟩
      exact ⟨L, mL, x, hL⟩
  · rintro ⟨L, mL, y, hy⟩
    obtain ⟨u, k', j, hu, ek, e⟩ := (dom_val ef hl k y).mp ⟨L, mL, hy⟩
    exact ⟨fun h => absurd h da, fun _ => ⟨u, hu, k', j, ek, by rw [e]; simp⟩⟩

/-- The maps hold atom keys outside every finite set when some line's tag allows atoms. -/
theorem atoms_inf (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) :
    AtomsInf (fun u => ∃ L ∈ lines, InMLine den L u) ↔ ∃ L ∈ lines, ∃ x, LineTag den L "atom" x := by
  constructor
  · intro h
    obtain ⟨u, hu, s, ns, hs⟩ := h NK
    cases e : u (.atom s) with
    | none => exact absurd e hs
    | some x =>
      rcases (unnamed_old ef hl hne lnNK ns (some x)).mp ⟨u, hu, e⟩ with h | ⟨y, h, L, mL, hy⟩
      · cases h
      · obtain rfl : x = y := Option.some.inj h
        exact ⟨L, mL, x, hy⟩
  · rintro ⟨L, mL, x, hx⟩ F
    obtain ⟨s, hs⟩ := fresh_str (F ++ NK)
    obtain ⟨u, hu, e⟩ := (unnamed_old ef hl hne lnNK (fun m => hs (List.mem_append_right _ m)) (some x)).mpr
      (Or.inr ⟨x, rfl, L, mL, hx⟩)
    exact ⟨u, hu, s, fun m => hs (List.mem_append_left _ m), by rw [e]; simp⟩

/-- The kinds whose keys the maps hold are those some line's tag allows. -/
theorem kind_held (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK)
    {d : String} (hd : d ∈ domainKinds) :
    KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
  by_cases da : d = "atom"
  · subst da
    rw [← atoms_inf ef hl hne lnNK]
    exact ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun h' => absurd rfl h'⟩⟩
  · obtain ⟨k, rfl⟩ := domKind_of hd da
    constructor
    · intro h
      obtain ⟨u, hu, k', i, ek, hi⟩ := h.2 da
      cases e : u (.dom k' i) with
      | none => exact absurd e hi
      | some x =>
        obtain rfl : k' = k := domKind_inj ek
        obtain ⟨L, mL, hL⟩ := (dom_val ef hl k' x).mpr ⟨u, k', i, hu, rfl, e⟩
        exact ⟨L, mL, x, hL⟩
    · rintro ⟨L, mL, y, hy⟩
      obtain ⟨u, k', j, hu, ek, e⟩ := (dom_val ef hl k y).mp ⟨L, mL, hy⟩
      exact ⟨fun h => absurd h da, fun _ => ⟨u, hu, k', j, ek, by rw [e]; simp⟩⟩

/-- `BoxRes` on the lines of a type is `BoxSem` on its maps. -/
theorem box_sem_iff (hne : lines ≠ []) {nt : Term} {nopt : Bool} {md : String}
    (S ks AK NK Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) (hks : ∀ s ∈ ks, s ∉ S)
    (hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ S) (akNK : ∀ s ∈ AK, s ∈ NK)
    (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) (orNK : ∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ S ∨ s ∈ ks)
    (hAt : "atom" ∈ Ds ∨ (md = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x))
    (hlen : Ds.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ds)
    {R : String → Prop} (hR : ∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧
      KeyNE den lines ks NK nt nopt md s ∧ ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s) (w : MW V) :
    BoxRes den lines ks AK NK R nt nopt md Ds w ↔
      BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) S nt nopt md Ds w := by
  classical
  let M : MW V → Prop := fun u => ∃ L ∈ lines, InMLine den L u
  have named : ∀ s o, (∃ L ∈ lines, LongM den L s o) ↔ Old M (.atom s) o := fun s o =>
    ⟨fun ⟨L, mL, u, hu, e⟩ => ⟨u, ⟨L, mL, hu⟩, e⟩, fun ⟨u, ⟨L, mL, hu⟩, e⟩ => ⟨L, mL, u, hu, e⟩⟩
  have eOld : ∀ s, (fun o => ∃ L ∈ lines, LongM den L s o) = Old M (.atom s) := fun s =>
    funext fun o => propext (named s o)
  have eSome : ∀ s, (∃ x, ∃ L ∈ lines, LongM den L s (some x)) = ∃ x, Old M (.atom s) (some x) := fun s =>
    propext (exists_congr fun x => named s (some x))
  have ksS : ∀ s ∈ NK, (s ∈ ks ↔ s ∉ S) := fun s ms => ⟨hks s, fun nS => by
    rcases orNK s ms with h | ⟨L, mL, hL⟩
    · exact ((hAK s).mp h).resolve_right nS
    · exact (lnKS L mL s hL).resolve_left nS⟩
  have SNK : ∀ s ∈ S, s ∈ NK := fun s m => akNK s ((hAK s).mpr (Or.inr m))
  have kh : ∀ d ∈ domainKinds, KindHeld M d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y :=
    fun d hd => kind_held ef hl hne lnNK hd
  have newDom : ∀ d ∈ domainKinds, ∀ x, NewDom den lines nt md d x ↔ NewDomS den M nt md d x := by
    intro d hd x; simp only [NewDom, NewDomS, kh d hd]
  have domNE : ∀ d ∈ domainKinds, DomNE den lines nt nopt md d ↔ DomNES den M nt nopt md d := by
    intro d hd; simp only [DomNE, DomNES, kh d hd]
  have atomK : "atom" ∈ domainKinds := by simp [domainKinds]
  -- Atoms no line names.
  have un0 : ∀ s, s ∉ NK → Old M (.atom s) none := fun s ns =>
    (unnamed_old ef hl hne lnNK ns none).mpr (Or.inl rfl)
  have unNE : ∀ s, s ∉ NK → ((∃ x, Old M (.atom s) (some x)) ↔ ∃ L ∈ lines, ∃ x, LineTag den L "atom" x) := by
    intro s ns
    constructor
    · rintro ⟨x, h⟩
      rcases (unnamed_old ef hl hne lnNK ns (some x)).mp h with h | ⟨y, h, L, mL, hy⟩
      · cases h
      · exact ⟨L, mL, y, hy⟩
    · rintro ⟨L, mL, x, hx⟩
      exact ⟨x, (unnamed_old ef hl hne lnNK ns (some x)).mpr (Or.inr ⟨x, rfl, L, mL, hx⟩)⟩
  have unNew : ∀ s, s ∉ NK → ∀ x, NewF den nt nopt md (Old M (.atom s)) (some x) ↔ NewDom den lines nt md "atom" x := by
    intro s ns x
    rw [newF_some (un0 s ns), NewDom, unNE s ns]
  have unNewE : ∀ s, s ∉ NK → (∃ x, NewF den nt nopt md (Old M (.atom s)) (some x)) = ∃ x, NewDom den lines nt md "atom" x :=
    fun s ns => propext (exists_congr (unNew s ns))
  have unKey : ∀ s, s ∉ NK → (KeyNES den M S nt nopt md s ↔ "atom" ∈ Ds ∧ DomNE den lines nt nopt md "atom") := by
    intro s ns
    have nS : s ∉ S := fun m => ns (SNK s m)
    rw [KeyNES, newF_ex (un0 s ns), unNE s ns]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨?_, h⟩
      rcases hAt with h' | ⟨hr, nt'⟩
      · exact h'
      · exfalso
        rcases h with h | ⟨h | ⟨L, mL, y, hy⟩, -⟩
        · rw [hr] at h; simp at h
        · rw [hr] at h; simp at h
        · exact nt' L mL y hy
    · rintro ⟨-, h⟩
      exact ⟨nS, h⟩
  have nameKey : ∀ s ∈ NK, (KeyNE den lines ks NK nt nopt md s ↔ KeyNES den M S nt nopt md s) := by
    intro s ms
    rw [KeyNE, KeyNES, eOld s, ksS s ms]
    simp [ms]
  have two : ∃ s₁ s₂, s₁ ∉ NK ∧ s₂ ∉ NK ∧ s₁ ≠ s₂ := by
    obtain ⟨s₁, h₁⟩ := fresh_str NK
    obtain ⟨s₂, h₂⟩ := fresh_str (s₁ :: NK)
    exact ⟨s₁, s₂, h₁, fun m => h₂ (List.mem_cons_of_mem _ m), fun e => h₂ (e ▸ List.mem_cons_self)⟩
  have swapE : (∃ x, ∃ L ∈ lines, LineTag den L "atom" x) = (∃ L ∈ lines, ∃ x, LineTag den L "atom" x) :=
    propext ⟨fun ⟨x, L, mL, h⟩ => ⟨L, mL, x, h⟩, fun ⟨L, mL, x, h⟩ => ⟨x, L, mL, h⟩⟩
  -- The updated keys and kinds.
  have updHas : ∀ A, UpdHas den lines ks NK nt nopt md Ds A ↔ UpdHasS den M S nt nopt md Ds A := by
    intro A
    constructor
    · rintro (⟨s, hk, h⟩ | ⟨d, md', hne', h⟩)
      · rw [eSome s, eOld s] at h
        exact Or.inl ⟨s, (nameKey s hk.1).mp hk, h⟩
      · by_cases da : d = "atom"
        · subst da
          obtain ⟨s, ns⟩ := fresh_str NK
          rw [swapE, ← propext (unNE s ns), ← unNewE s ns] at h
          exact Or.inl ⟨s, (unKey s ns).mpr ⟨md', hne'⟩, h⟩
        · obtain ⟨k, rfl⟩ := domKind_of (hD _ md') da
          rw [propext (exists_congr (dom_val ef hl k)), propext (exists_congr (newDom _ (domKind_mem k)))] at h
          exact Or.inr ⟨_, md', da, (domNE _ (domKind_mem k)).mp hne', h⟩
    · rintro (⟨s, hk, h⟩ | ⟨d, md', da, hne', h⟩)
      · by_cases ms : s ∈ NK
        · rw [← eSome s, ← eOld s] at h
          exact Or.inl ⟨s, (nameKey s ms).mpr hk, h⟩
        · obtain ⟨ha, hd⟩ := (unKey s ms).mp hk
          rw [propext (unNE s ms), unNewE s ms, ← swapE] at h
          exact Or.inr ⟨"atom", ha, hd, h⟩
      · obtain ⟨k, rfl⟩ := domKind_of (hD _ md') da
        rw [← propext (exists_congr (dom_val ef hl k)), ← propext (exists_congr (newDom _ (domKind_mem k)))] at h
        exact Or.inr ⟨_, md', (domNE _ (domKind_mem k)).mpr hne', h⟩
  -- Replacing.
  have noA : ∀ {s}, RS den M S nt nopt md Ds s → ¬("atom" ∈ Ds ∧ DomNE den lines nt nopt md "atom") := by
    rintro s ⟨-, -, -, uq⟩ h
    obtain ⟨s₁, s₂, n₁, n₂, ne⟩ := two
    exact ne ((uq s₁ ((unKey s₁ n₁).mpr h)).trans (uq s₂ ((unKey s₂ n₂).mpr h)).symm)
  have rIff : ∀ s, R s ↔ RS den M S nt nopt md Ds s := by
    intro s
    rw [hR]
    constructor
    · rintro ⟨hr, nd, hk, uq⟩
      refine ⟨hr, fun d md' _ h => nd d md' ((domNE d (hD d md')).mpr h), (nameKey s hk.1).mp hk, fun s' hk' => ?_⟩
      by_cases ms' : s' ∈ NK
      · exact uq s' ((nameKey s' ms').mpr hk')
      · obtain ⟨ha, hd⟩ := (unKey s' ms').mp hk'
        exact absurd hd (nd _ ha)
    · intro h
      have nA := noA h
      obtain ⟨hr, nd, hk, uq⟩ := h
      have ms : s ∈ NK := Classical.byContradiction fun ns => nA ((unKey s ns).mp hk)
      refine ⟨hr, fun d md' hd => ?_, (nameKey s ms).mpr hk, fun s' hk' => uq s' ((nameKey s' hk'.1).mp hk')⟩
      by_cases da : d = "atom"
      · subst da; exact nA ⟨md', hd⟩
      · exact nd d md' da ((domNE d (hD d md')).mp hd)
  have unR : ∀ s, s ∉ NK → ¬RS den M S nt nopt md Ds s := fun s ns h =>
    noA h ((unKey s ns).mp h.2.2.1)
  have atomIn : ∀ x, NewDom den lines nt md "atom" x → "atom" ∈ Ds := fun x hx => by
    rcases hAt with h | ⟨hr, nt'⟩
    · exact h
    · exfalso
      rcases hx.2 with h | ⟨L, mL, y, hy⟩
      · rw [hr] at h; simp at h
      · exact nt' L mL y hy
  -- The box.
  have syn : BoxSynG den lines ks NK R nt nopt md Ds w ↔ SynS den M S nt nopt md Ds w := by
    constructor
    · rintro ⟨hn, hu, hd⟩
      refine ⟨fun s => ?_, fun k i => ?_⟩
      · by_cases ms : s ∈ NK
        · by_cases sS : s ∈ S
          · refine Or.inl ⟨sS, ?_⟩
            rcases hn s ms with ⟨-, h⟩ | ⟨sk, -⟩
            · exact (named s _).mp h
            · exact absurd sS (hks s sk)
          · refine Or.inr ⟨sS, ?_⟩
            rcases hn s ms with ⟨nr, h⟩ | ⟨-, h⟩
            · exact Or.inl ⟨fun h' => nr ((rIff s).mpr h'), (named s _).mp h⟩
            · rw [eOld s] at h; exact Or.inr h
        · have sS : s ∉ S := fun m => ms (SNK s m)
          refine Or.inr ⟨sS, ?_⟩
          rcases hu s ms with h | ⟨x, h, hx | ⟨-, hx⟩⟩
          · exact Or.inl ⟨unR s ms, by rw [h]; exact un0 s ms⟩
          · exact Or.inl ⟨unR s ms, (unnamed_old ef hl hne lnNK ms _).mpr (Or.inr ⟨x, h, hx⟩)⟩
          · rw [h]; exact Or.inr ((unNew s ms x).mpr hx)
      · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, Or.inl ((dom_val ef hl k x).mp hx)⟩
        · exact Or.inr ⟨x, h, Or.inr ⟨dk, (newDom _ (domKind_mem k) x).mp hx⟩⟩
    · rintro ⟨ha, hd⟩
      refine ⟨fun s ms => ?_, fun s ms => ?_, fun k i => ?_⟩
      · rcases ha s with ⟨sS, h⟩ | ⟨sS, ⟨nr, h⟩ | h⟩
        · refine Or.inl ⟨fun hr => ?_, (named s _).mpr h⟩
          obtain ⟨-, -, hk, -⟩ := (hR s).mp hr
          exact hks s hk.2.1 sS
        · exact Or.inl ⟨fun hr => nr ((rIff s).mp hr), (named s _).mpr h⟩
        · refine Or.inr ⟨(ksS s ms).mpr sS, ?_⟩
          rw [eOld s]; exact h
      · rcases ha s with ⟨sS, -⟩ | ⟨-, ⟨-, h⟩ | h⟩
        · exact absurd (SNK s sS) ms
        · rcases (unnamed_old ef hl hne lnNK ms _).mp h with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', Or.inl hx⟩
        · cases e : w (.atom s) with
          | none => exact Or.inl rfl
          | some x =>
            rw [e] at h
            have hx := (unNew s ms x).mp h
            exact Or.inr ⟨x, rfl, Or.inr ⟨atomIn x hx, hx⟩⟩
      · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, Or.inl ((dom_val ef hl k x).mpr hx)⟩
        · exact Or.inr ⟨x, h, Or.inr ⟨dk, (newDom _ (domKind_mem k) x).mpr hx⟩⟩
  have unset : SynS den M S nt nopt md Ds w → (UnsetSemD den ks AK Ds nt w ↔ UnsetS den S Ds nt w) := by
    intro hs
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun s sS => ?_, h2⟩
      by_cases sk : s ∈ ks
      · exact h1 s (Or.inl sk)
      have sAK : s ∉ AK := fun m => ((hAK s).mp m).elim sk sS
      by_cases ha : "atom" ∈ Ds
      · exact h1 s (Or.inr ⟨ha, sk, sAK⟩)
      have ms : s ∉ NK := fun ms => sk ((ksS s ms).mpr sS)
      obtain ⟨hr, nt'⟩ := hAt.resolve_left ha
      rcases hs.1 s with ⟨sS', -⟩ | ⟨-, ⟨-, h⟩ | h⟩
      · exact absurd sS' sS
      · rcases (unnamed_old ef hl hne lnNK ms _).mp h with h' | ⟨x, -, L, mL, hx⟩
        · exact Or.inl h'
        · exact absurd hx (nt' L mL x)
      · cases e : w (.atom s) with
        | none => exact Or.inl rfl
        | some x =>
          rw [e] at h
          exact absurd (atomIn x ((unNew s ms x).mp h)) ha
    · rintro ⟨h1, h2⟩
      refine ⟨fun s hs' => ?_, h2⟩
      rcases hs' with sk | ⟨-, -, sAK⟩
      · exact h1 s (hks s sk)
      · exact h1 s fun m => sAK ((hAK s).mpr (Or.inr m))
  have eM : (∀ L ∈ lines, ¬InMLine den L wNone) ↔ ¬M wNone :=
    ⟨fun h ⟨L, mL, hL⟩ => h L mL hL, fun h L mL hL => h ⟨L, mL, hL⟩⟩
  have present : BoxPresent den lines ks NK nt nopt md Ds ↔ PresentS den M S nt nopt md Ds := by
    unfold BoxPresent PresentS
    rw [updHas, updHas, eM]
  have same : BoxSame den lines ks NK nt nopt md Ds ↔ SameS den M S nt nopt md Ds := by
    unfold BoxSame SameS
    rw [updHas]
  have pre : ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ↔
      UpdHasS den M S nt nopt md Ds (fun _ _ => True) := by
    rw [← updHas]
    simp [UpdHas]
  have hlen' : (Ds.length ≠ 12) ↔ ¬∀ d ∈ domainKinds, d ∈ Ds := not_congr hlen
  unfold BoxRes BoxSem
  rw [pre, same, present, hlen']
  constructor
  · rintro ⟨hp, hs, hn⟩
    refine ⟨hp, hs, fun ns => ?_⟩
    obtain ⟨hb, hq⟩ := hn ns
    have hb' := syn.mp hb
    exact ⟨hb', fun hpr => ⟨fun hc hu => (hq hpr).1 hc ((unset hb').mpr hu), (hq hpr).2⟩⟩
  · rintro ⟨hp, hs, hn⟩
    refine ⟨hp, hs, fun ns => ?_⟩
    obtain ⟨hb, hq⟩ := hn ns
    exact ⟨syn.mpr hb, fun hpr => ⟨fun hc hu => (hq hpr).1 hc ((unset hb).mp hu), (hq hpr).2⟩⟩

end lines

end

end Elixir.STTDescrProofsTest.Nest

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
        Elixir.Module.Types.Descr.«opt_union/2», ru, Erlang.erlang.«==/2», equal_eq_decide]
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
            simp [boolAtom, Term.list, hc, Erlang.erlang.«/=/2»]
          · refine ⟨_, ⟨Bool.true, val, .atom "atom" :: mis, T, rfl, hT, semT rfl, by simp, mis',
              vKeep (fun h => by have := heldI.mpr h; cases this), fun _ => rfl⟩, ?_⟩
            simp [boolAtom, Term.list, hc, Erlang.erlang.«/=/2»]
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
          · simp [boolAtom, Term.list, ne])
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
    (_sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (lines : List Term)
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
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  cases keep
  · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1»,
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
      simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self]
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
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, rW]
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
  · simp [splitT, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
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
      · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp, Or.inl ⟨rfl, emp⟩⟩
        cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
          simp [rN1, rN2, rr]
      · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simp,
          Or.inr ⟨r, rfl, fr, sr⟩⟩
        cases f₁ <;> simp [Term.list, boolAtom, Lynx.Except.orElse, Lynx.Term.compare_self] at rN1 rN2 ⊢ <;>
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
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
            getMapKeys_single, lc, Option.toList] at rN1 rN2 ⊢ <;> simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [dne', boolAtom, Lynx.Except.orElse, rKs, rW, neR,
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
  cases keep
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      modeT, r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, mk0, Erlang.sets.«to_list/1»,
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
        simp [hL', rZ, Term.list]
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
      modeT, r₁', r₂', rE', Erlang.erlang.«--/2», Term.properList?, mk0, Erlang.sets.«to_list/1»,
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
