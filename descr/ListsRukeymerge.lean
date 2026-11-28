module

public import Erlang.program
public import MapSplitPairs
public import TupleInsertElements
public import ListsSortCompare

@[expose] public section

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem le_ne_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isLE = true) (ne : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel a b) a b = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem le_le {a b : Term} (h : Term.compare (Term.fuel a b) a b = .lt) : (Term.compare (Term.fuel a b) a b).isLE = true := by
  simp [h]

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem preD_BC {M B C : List Term} (p : PreD κ Kd M [] B C) : PreD κ Kd M B C [] :=
  ⟨p.sm, p.sb, p.sc, SD_nil, p.kb, p.kc, fun _ h => by simp at h, p.ub, p.uc, fun _ h => by simp at h⟩

theorem preD_AC {M A C : List Term} (p : PreD κ Kd M A [] C) : PreD κ Kd M A C [] :=
  ⟨p.sm, p.sa, p.sc, SD_nil, p.ka, p.kc, fun _ h => by simp at h, p.ua, p.uc, fun _ h => by simp at h⟩

/-- The head of a descending source is above the rest of it. -/
theorem sd_head {x y : Term} {B : List Term} (s : SD κ (x :: y :: B)) :
    Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt := c_lt_of_gt ((SD_cons.1 s).1 y (by simp))

end

section
variable {I : Term} {κ : Term → Term}

theorem rkm2 (n : Nat) :
    (∀ T1 H2 T2 M, 2 * (List.length T1 + List.length T2 + 1) + 1 ≤ n → (PreD κ (KdK I κ)) M T1 (H2 :: T2) [] →
      ∃ R, Erlang.lists.«rukeymerge2_1/6» I (Term.list T1) (κ H2) (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ ResD κ M T1 (H2 :: T2) [] R) ∧
    (∀ H1 T1 H2M T2 M, 2 * (List.length T1 + List.length T2 + 2) ≤ n → (PreD κ (KdK I κ)) M (H1 :: T1) (H2M :: T2) [] →
      (Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge2_2/8» I (Term.list T1) (κ H1) (Term.list T2) (Term.list M)
        (κ H2M) H2M H1 = .ok (Term.list R) ∧ ResD κ M (H1 :: T1) (H2M :: T2) [] R) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro T1 H2 T2 M len p
    rw [Erlang.lists.«rukeymerge2_1/6».eq_def]
    cases T1 with
    | nil =>
      obtain ⟨p', tr⟩ := pushDB p (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T2 (H2 :: M), tr _ (resD_congr (by simp) (resD_fin p'.sm p'.sb p'.ub))⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      simp only [k1, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 M (by simp at len; omega) p c12
      simp only [c12]
      obtain ⟨p', tr⟩ := pushDA p (by simpa using not_le_lt c12) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p'
      exact ⟨R, by simpa using run, tr R res⟩
  · intro H1 T1 H2M T2 M len p c1
    rw [Erlang.lists.«rukeymerge2_2/8».eq_def]
    cases T2 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
        exact ⟨_, by simpa using rev2 T1 (H1 :: M), tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T1 (H1 :: H2M :: M),
        tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      have s2 := sd_head p.sb
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simp)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 (H2M :: M) (by simp at len; omega) p1 c12
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: H2M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩

theorem rkm3 (n : Nat) :
    (∀ T1 H2 T2 H3 T3 M D1 D2, 2 * (List.length T1 + List.length T2 + List.length T3 + 2) + 1 ≤ n →
      (PreD κ (KdK I κ)) M T1 (H2 :: T2) (H3 :: T3) →
      ∃ R, Erlang.lists.«rukeymerge3_1/11» I (Term.list T1) D1 D2 (κ H2) H2 (Term.list T2) (Term.list M)
        (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧ ResD κ M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2M T2 H3 T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2M :: T2) (H3 :: T3) → (Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M)).isLE = true →
      Term.compare (Term.fuel (κ H3) (κ H2M)) (κ H3) (κ H2M) = .lt →
      ∃ R, Erlang.lists.«rukeymerge3_2/11» I (κ H1) H1 (Term.list T1) (Term.list T2) H2M (κ H2M)
        (Term.list M) (κ H3) H3 (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2M :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true →
      (Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge3_12_3/11» I (κ H1) H1 (Term.list T1) (κ H2) H2 (Term.list T2)
        (Term.list M) (κ H3M) H3M (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD κ (KdK I κ)) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → Term.compare (Term.fuel (κ H2) (κ H1)) (κ H2) (κ H1) = .lt →
      (Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M)).isLE = true →
      ∃ R, Erlang.lists.«rukeymerge3_21_3/11» I (κ H1) H1 (Term.list T1) (κ H2) H2 (Term.list T2)
        (Term.list M) (κ H3M) H3M (Term.list T3) = .ok (Term.list R) ∧
        ResD κ M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := rkm2 (I := I) (κ := κ) n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- rukeymerge3_1
    intro T1 H2 T2 H3 T3 M D1 D2 len p
    rw [Erlang.lists.«rukeymerge3_1/11».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H2 T2 H3 T3 M (by simp at len; omega) (preD_BC p) c23
        exact ⟨R, run, resD_congr (by simp) res⟩
      simp only [c23]
      obtain ⟨p1, tr1⟩ := pushDB p (by simp) (by simpa using not_le_lt c23)
      obtain ⟨R, run, res⟩ := m2.1 T2 H3 T3 (H2 :: M) (by simp at len; omega) (preD_BC p1)
      exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
    | cons H1 T1 =>
      have k1 := (p.ka H1 (by simp)).1
      simp only [k1, Lynx.Except.ok_bind, le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
        · simp only [c23, ↓reduceIte]
          exact ih12 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 c23
        simp only [c23]
        exact ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 (not_le_lt c23)
      simp only [c12]
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        exact ih21 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p (not_le_lt c12) c13
      simp only [c13]
      obtain ⟨p1, tr1⟩ := pushDA p (by simpa using not_le_lt c12) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) D1 D2 (by simp at len; omega) p1
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_2
    intro H1 T1 H2M T2 H3 T3 M len p c1 c3
    rw [Erlang.lists.«rukeymerge3_2/11».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: M) (by simp at len; omega) (preD_AC p2)
        exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H3 T3 (H2M :: M) (by simp at len; omega) (preD_AC p1) c13
        exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
      simp only [c13]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: H2M :: M) (by simp at len; omega) (preD_AC p2)
      exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
    | cons H2 T2 =>
      have k2 := (p.kb H2 (by simp)).1
      have s2 := sd_head p.sb
      simp only [k2, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel (κ H1) (κ H2)) (κ H1) (κ H2)).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simpa using c3)
        by_cases c23 : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
        · simp only [c23, ↓reduceIte]
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12 c23
          exact ⟨R, by simpa using run, tr1 R res⟩
        simp only [c23]
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12
          (not_le_lt c23)
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H2M)) (κ H1) (κ H2M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) H1 (Term.list T1) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c21 c13
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H2M :: M) H1 (Term.list T1)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
  · -- rukeymerge3_12_3
    intro H1 T1 H2 T2 H3M T3 M len p c12 c23
    rw [Erlang.lists.«rukeymerge3_12_3/11».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 M (by simp at len; omega) p1 c12
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 (H3M :: M) (by simp at len; omega) p1 c12
      exact ⟨R, by simpa using run, tr1 R res⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      have s3 := sd_head p.sc
      simp only [k3, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c23' : (Term.compare (Term.fuel (κ H2) (κ H3)) (κ H2) (κ H3)).isLE = true
      · simp only [c23', ↓reduceIte]
        have l23 := c_le_lt c23' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c23'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c23']
      have c32 := not_le_lt c23'
      by_cases e : Term.compare (Term.fuel (κ H2) (κ H3M)) (κ H2) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p1 c12 c32
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c32
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_21_3
    intro H1 T1 H2 T2 H3M T3 M len p c21 c13
    rw [Erlang.lists.«rukeymerge3_21_3/11».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: H3M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
    | cons H3 T3 =>
      have k3 := (p.kc H3 (by simp)).1
      have s3 := sd_head p.sc
      simp only [k3, Lynx.Except.ok_bind, le_ok, eq_ok, g_if]
      by_cases c13' : (Term.compare (Term.fuel (κ H1) (κ H3)) (κ H1) (κ H3)).isLE = true
      · simp only [c13', ↓reduceIte]
        have l13 := c_le_lt c13' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c21 c13'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13']
      have c31 := not_le_lt c13'
      by_cases e : Term.compare (Term.fuel (κ H1) (κ H3M)) (κ H1) (κ H3M) = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) H1 (Term.list T1) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H3M :: M) H1 (Term.list T1)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

theorem eqv_ne_nil {R S : List Term} (e : Eqv κ R S) (h : S ≠ []) : R ≠ [] := by
  obtain ⟨x, S', rfl⟩ := List.exists_cons_of_ne_nil h
  intro hr
  have := e (κ x)
  simp [hr, lk_cons] at this

theorem lk_mem {s z : Term} {A : List Term} (h : lk κ s A = some z) : z ∈ A := by
  induction A with
  | nil => simp at h
  | cons y ys ih =>
    by_cases e : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq
    · simp [lk_cons, e] at h; simp [h]
    · simp [lk_cons, e] at h; simp [ih h]

theorem lk_self {x : Term} {A : List Term}
    (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (hx : x ∈ A) :
    lk κ (κ x) A = some x := by
  induction A with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons] at hx
    by_cases e : x = y
    · subst e; simp [lk_cons]
    · have hx' : x ∈ ys := hx.resolve_left e
      simp [lk_cons, h.1 x hx', ih h.2 hx']

theorem mem_of_eqv {R S : List Term} {x : Term}
    (h : R.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (e : Eqv κ R S) (hx : x ∈ R) :
    x ∈ S := lk_mem ((e (κ x)).symm.trans (lk_self h hx))

theorem eqv_acc {R M X : List Term} (P Q : List Term) (er : Eqv κ R (P ++ M ++ Q)) (em : Eqv κ M X) :
    Eqv κ R (P ++ X ++ Q) := er.trans (((Eqv.refl P).append em).append (Eqv.refl Q))

/-- Members of a merge of keyed sources are keyed. -/
theorem kd_of_eqv {Kd : Term → Prop} {M S : List Term}
    (h : M.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) (e : Eqv κ M S)
    (k : ∀ x ∈ S, Kd x) : ∀ x ∈ M, Kd x := fun x hx => k x (mem_of_eqv h e hx)

/-- Nonempty runs of keyed elements, ascending or descending. -/
def RunsA (Kd : Term → Prop) (Rs : List (List Term)) : Prop :=
  ∀ r ∈ Rs, r ≠ [] ∧ SA κ r ∧ ∀ x ∈ r, Kd x

def RunsD (Kd : Term → Prop) (Rs : List (List Term)) : Prop :=
  ∀ r ∈ Rs, r ≠ [] ∧ SD κ r ∧ ∀ x ∈ r, Kd x

end

section
variable {I : Term} {κ : Term → Term}

theorem ukm_mergel (n : Nat) :
    (∀ Rs Acc, 4 * (List.length Rs + List.length Acc) + 2 * min (List.length Acc) 1 ≤ n →
      1 ≤ List.length Rs + List.length Acc → RunsA (κ := κ) (KdK I κ) Rs → RunsD (κ := κ) (KdK I κ) Acc →
      ∃ R, Erlang.lists.«ukeymergel/3» I (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list)) =
        .ok (Term.list R) ∧ SA κ R ∧ Eqv κ R (Acc.reverse.flatten ++ Rs.flatten)) ∧
    (∀ Rs Acc, 4 * (List.length Rs + List.length Acc) + 2 * min (List.length Acc) 1 + 1 ≤ n →
      1 ≤ List.length Rs + List.length Acc → RunsD (κ := κ) (KdK I κ) Rs → RunsA (κ := κ) (KdK I κ) Acc →
      ∃ R, Erlang.lists.«rukeymergel/3» I (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list)) =
        .ok (Term.list R) ∧ SA κ R ∧ Eqv κ R (Rs.reverse.flatten ++ Acc.flatten)) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro Rs Acc len one ra rd
    rw [Erlang.lists.«ukeymergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih2 Acc [] (by simp at len one ⊢; omega) (by simpa using one) rd
        (by simp [RunsA])
      exact ⟨R, run, sr, by simpa using er⟩
    | [L] =>
      cases Acc with
      | nil =>
        obtain ⟨_, sl, _⟩ := ra L (by simp)
        exact ⟨L, by simp, sl, by simpa using Eqv.refl L⟩
      | cons A Acc =>
        obtain ⟨nl, sl, kl⟩ := ra L (by simp)
        have rv := rev2 L []
        simp only [List.append_nil] at rv
        simp only [List.map_cons, List.map_nil, ← Term.list_nil, rv,
          Lynx.Except.ok_bind]
        obtain ⟨R, run, sr, er⟩ := ih2 (L.reverse :: A :: Acc) [] (by simp at len ⊢; omega) (by simp)
          (by
            intro r hr
            simp only [List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact ⟨by simpa using nl, SD_reverse.2 sl, fun x hx => kl x (by simpa using hx)⟩
            · exact rd r (by simp [hr]))
          (by simp [RunsA])
        refine ⟨R, by simpa using run, sr, er.trans ?_⟩
        simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
        exact Eqv.append (Eqv.refl _) (Eqv.append (Eqv.refl _) (eqv_reverse sl.ne))
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨H1, T1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      have e1 := (k1 H1 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (ukm2 (I := I) (κ := κ) (T1.length + 1 + (H2 :: T2).length)).2 T1 H1 (H2 :: T2) []
        (by omega) ⟨SD_nil, s1, s2, SA_nil, k1, k2, by simp, fun _ _ _ h => by simp at h,
          fun _ _ => Or.inl fun _ h => by simp at h, by simp⟩ (fun _ _ _ h => by simp at h)
      simp only [List.map_cons, List.map_nil, e1, run,
        Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih1 [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
        (by simp [RunsA]) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.append_nil, List.mem_append] at hx
              rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)⟩
          · exact rd r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc Acc.reverse.flatten [] (by simpa using er) em
      simpa using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨_, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := ra r3 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H3, T3, rfl⟩ := List.exists_cons_of_ne_nil n3
      have e2 := (k2 H2 (by simp)).1
      have e3 := (k3 H3 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (ukm3 (I := I) (κ := κ) (r1.length + T2.length + T3.length + 2)).1
        r1 T2 T3 [] H2 H3 (.cons H2 H3) (Term.list (Acc.map Term.list)) (by omega)
        ⟨SD_nil, s1, s2, s3, k1, k2, k3, fun _ _ _ h => by simp at h,
          fun _ _ => Or.inl fun _ h => by simp at h, fun _ _ => Or.inl fun _ h => by simp at h⟩
        (fun x hx => by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
          rcases hx with h | h | h | h
          · subst h; exact (k2 x (by simp)).2 _ _
          · exact (k2 x (by simp [h])).2 _ _
          · subst h; exact (k3 x (by simp)).2 _ _
          · exact (k3 x (by simp [h])).2 _ _)
      simp only [List.map_cons, e2, e3, run, Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih1 L (M :: Acc) (by simp at len ⊢; omega) (by simp only [List.length_cons]; omega)
        (fun r hr => ra r (by simp [hr])) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.mem_append] at hx
              rcases hx with (hx | hx) | hx
              · exact k1 x hx
              · exact k2 x hx
              · exact k3 x hx)⟩
          · exact rd r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc Acc.reverse.flatten L.flatten (by simpa using er) em
      simpa using this
  · intro Rs Acc len one rd ra
    rw [Erlang.lists.«rukeymergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih1 Acc [] (by simp at len one ⊢; omega) (by simpa using one) ra
        (by simp [RunsD])
      exact ⟨R, run, sr, by simpa using er⟩
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := rd L (by simp)
      have rv := rev2 L []
      simp only [List.append_nil] at rv
      simp only [List.map_cons, List.map_nil, ← Term.list_nil, rv,
        Lynx.Except.ok_bind]
      obtain ⟨R, run, sr, er⟩ := ih1 (L.reverse :: Acc) [] (by simp at len ⊢; omega) (by simp)
        (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨by simpa using nl, SA_reverse.2 sl, fun x hx => kl x (by simpa using hx)⟩
          · exact ra r hr)
        (by simp [RunsD])
      refine ⟨R, by simpa using run, sr, er.trans ?_⟩
      simp only [List.reverse_nil, List.flatten_nil, List.nil_append, List.flatten_cons,
        List.reverse_cons, List.append_nil]
      exact Eqv.append (eqv_reverse sl.ne) (Eqv.refl _)
    | [r2, r1] =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H1, T1, rfl⟩ := List.exists_cons_of_ne_nil n1
      have e2 := (k2 H2 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (rkm2 (I := I) (κ := κ) (2 * ((H1 :: T1).length + T2.length + 1) + 1)).1
        (H1 :: T1) H2 T2 [] (by omega) ⟨SA_nil, s1, s2, SD_nil, k1, k2, by simp, fun _ _ _ h => by simp at h,
          fun _ _ _ h => by simp at h, by simp⟩
      simp only [List.map_cons, List.map_nil, e2, run,
        Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih2 [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
        (by simp [RunsD]) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.append_nil, List.mem_append] at hx
              rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)⟩
          · exact ra r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc [] Acc.flatten (by simpa using er) em
      simpa using this
    | r3 :: r2 :: r1 :: L =>
      obtain ⟨_, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := rd r3 (by simp)
      obtain ⟨H2, T2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨H3, T3, rfl⟩ := List.exists_cons_of_ne_nil n3
      have e2 := (k2 H2 (by simp)).1
      have e3 := (k3 H3 (by simp)).1
      obtain ⟨M, run, sm, em⟩ := (rkm3 (I := I) (κ := κ)
        (2 * (r1.length + T2.length + T3.length + 2) + 1)).1
        r1 H2 T2 H3 T3 [] (Term.list (Acc.map Term.list)) .nil (by omega)
        ⟨SA_nil, s1, s2, s3, k1, k2, k3, fun _ _ _ h => by simp at h,
          fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
      simp only [List.map_cons, e2, e3, run, Lynx.Except.ok_bind]
      obtain ⟨R, run', sr, er⟩ := ih2 L (M :: Acc) (by simp at len ⊢; omega) (by simp only [List.length_cons]; omega)
        (fun r hr => rd r (by simp [hr])) (by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact ⟨eqv_ne_nil em (by simp), sm, kd_of_eqv sm.ne em (by
              intro x hx; simp only [List.nil_append, List.mem_append] at hx
              rcases hx with (hx | hx) | hx
              · exact k1 x hx
              · exact k2 x hx
              · exact k3 x hx)⟩
          · exact ra r hr)
      refine ⟨R, by simpa using run', sr, ?_⟩
      have := eqv_acc L.reverse.flatten Acc.flatten (by simpa using er) em
      simpa using this

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

/-- An element moved into the middle of a run, past keys it does not share. -/
theorem ins_mid {P A B L : List Term} {z : Term}
    (h : ∀ y ∈ A ++ B, Term.compare (Term.fuel (κ y) (κ z)) (κ y) (κ z) ≠ .eq) :
    Eqv κ (P ++ (A ++ z :: B) ++ L) (P ++ (A ++ B) ++ z :: L) := by
  have e1 := eqv_move (κ := κ) (A := A) (B := B ++ L) (x := z) (fun y hy => h y (by simp [hy]))
  have e2 := eqv_move (κ := κ) (A := A ++ B) (B := L) (x := z) h
  simp only [List.append_assoc] at e1 e2 ⊢
  exact (Eqv.refl P).append (e1.trans e2.symm)

theorem drop_at {P L : List Term} {y z : Term} (hy : y ∈ P) (e : Term.compare (Term.fuel (κ y) (κ z)) (κ y) (κ z) = .eq) :
    Eqv κ (P ++ L) (P ++ z :: L) := (eqv_drop hy e).symm

theorem not_islt {a b : Term} (h : ¬Term.compare (Term.fuel a b) a b = .lt) : ¬(Term.compare (Term.fuel a b) a b).isLT = true := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem lt_swap_of {a b : Term} (e : ¬Term.compare (Term.fuel a b) a b = .eq) (l : ¬Term.compare (Term.fuel a b) a b = .lt) :
    Term.compare (Term.fuel b a) b a = .lt := by
  cases e' : Term.compare (Term.fuel a b) a b
  · exact absurd e' l
  · exact absurd e' e
  · exact c_lt_of_gt e'

theorem nil_cmp {R : List Term} : Term.compare (Term.fuel (Term.list R) .nil) (Term.list R) .nil = .eq ↔ R = [] := by
  cases R <;> simp

end

section
variable {I : Term} {κ : Term → Term}

theorem uks1_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SD κ (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, (KdK I κ) x) (rs : RunsD (κ := κ) (KdK I κ) Rs) :
    ∃ Res, Erlang.lists.«ukeysplit_1/8» I X (κ X) Y (κ Y) (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA κ Res ∧
      Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«ukeysplit_1/8».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (ukm_mergel (I := I) (κ := κ) (4 * (Rs.length + 2) + 1)).2
    ((Y :: X :: R) :: Rs) [] (by simp; omega) (by simp) (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr) (by simp [RunsA])
  exact ⟨Res, by simpa using run, sr, by simpa using er⟩

theorem uks11_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SD κ (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, (KdK I κ) x) (ks : (KdK I κ) S) (rs : RunsD (κ := κ) (KdK I κ) Rs) :
    ∃ Res, Erlang.lists.«ukeysplit_1_1/10» I X (κ X) Y (κ Y) (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S (κ S) = .ok (Term.list Res) ∧ SA κ Res ∧
      Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«ukeysplit_1_1/10».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (ukm_mergel (I := I) (κ := κ) (4 * (Rs.length + 3) + 1)).2
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp) (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact ⟨by simp, by simp [SD], by simpa using ks⟩
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr) (by simp [RunsA])
  exact ⟨Res, by simpa using run, sr, by simpa using er⟩

theorem uks1 (n : Nat) :
    (∀ X Y L R Rs, List.length L ≤ n → SD κ (Y :: X :: R) → (∀ x ∈ Y :: X :: R, (KdK I κ) x) →
      RunsD (κ := κ) (KdK I κ) Rs → (∀ x ∈ L, (KdK I κ) x) →
      ∃ Res, Erlang.lists.«ukeysplit_1/8» I X (κ X) Y (κ Y) (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA κ Res ∧
        Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, List.length L ≤ n → SD κ (Y :: X :: R) → (∀ x ∈ Y :: X :: R, (KdK I κ) x) →
      Term.compare (Term.fuel (κ S) (κ X)) (κ S) (κ X) = .lt → (KdK I κ) S → RunsD (κ := κ) (KdK I κ) Rs → (∀ x ∈ L, (KdK I κ) x) →
      ∃ Res, Erlang.lists.«ukeysplit_1_1/10» I X (κ X) Y (κ Y) (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S (κ S) = .ok (Term.list Res) ∧ SA κ Res ∧
        Eqv κ Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact uks1_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact uks11_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact uks1_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt := c_lt_of_gt (sc'.1 X (by simp))
    rw [Erlang.lists.«ukeysplit_1/8».eq_def]
    simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
    by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) e1
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have zy : Term.compare (Term.fuel (κ Z) (κ Y)) (κ Z) (κ Y) ≠ .eq := fun e => e1 (c_eq_symm e)
    by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
    · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
      have gz := SD.gt_all sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := gz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l1' := not_islt l1
    simp only [l1', Bool.false_eq_true, ↓reduceIte]
    have gzy := lt_swap_of e1 l1
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) e2
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have sx := SD_cons.1 sc'.2
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      have gzx := SD.gt_all sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih1 Z Y L (X :: R) Rs len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
          rcases hy with rfl | hy
          · intro e; exact zy (c_eq_symm e)
          · have := gzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l2' := not_islt l2
    simp only [l2', Bool.false_eq_true, ↓reduceIte]
    have gzx := lt_swap_of e2 l2
    cases R with
    | nil =>
      simp only [Term.compare_self, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L [Z] Rs len'
        (by simp [SD]; exact ⟨⟨sc'.1 X (by simp), c_gt_of_lt (c_lt_trans gzx yx)⟩, c_gt_of_lt gzx⟩)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact kc x (by simp)
          · exact kc x (by simp)
          · exact kz)
        rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
    | cons r R =>
      have : ¬Term.compare (Term.fuel (Term.list (r :: R)) .nil) (Term.list (r :: R)) .nil = .eq := by simp
      simp only [this, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc gzx kz rs kl'
      exact ⟨Res, run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc sx ks rs kl
    cases L with
    | nil => exact uks11_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt := c_lt_of_gt (sc'.1 X (by simp))
    have sy := c_lt_trans sx yx
    rw [Erlang.lists.«ukeysplit_1_1/10».eq_def]
    simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
    by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) e1
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have zy : Term.compare (Term.fuel (κ Z) (κ Y)) (κ Z) (κ Y) ≠ .eq := fun e => e1 (c_eq_symm e)
    by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
    · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
      have gz := SD.gt_all sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        sy ks rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · have := gz y hy; rw [c_swap, this]; simp
          · rw [c_lt_trans sy l1]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l1' := not_islt l1
    simp only [l1', Bool.false_eq_true, ↓reduceIte]
    have gzy := lt_swap_of e1 l1
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) e2
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      have gzx := SD.gt_all sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih2 Z Y L (X :: R) Rs S len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        (c_lt_trans sx l2) ks rs kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, gzx _ (by simp)]; simp
          · rw [c_swap, gzx y (by simp [hy])]; simp
          · rw [c_lt_trans sx l2]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l2' := not_islt l2
    simp only [l2', Bool.false_eq_true, ↓reduceIte]
    have rs' : RunsD (κ := κ) (KdK I κ) ((Y :: X :: R) :: Rs) := by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨by simp, sc, kc⟩
      · exact rs r hr
    by_cases e3 : Term.compare (Term.fuel (κ S) (κ Z)) (κ S) (κ Z) = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) e3
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    by_cases l3 : Term.compare (Term.fuel (κ S) (κ Z)) (κ S) (κ Z) = .lt
    · simp only [l3, Ordering.isLT_lt, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SD]; exact c_gt_of_lt l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := κ) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; exact e3)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    have l3' := not_islt l3
    simp only [l3', Bool.false_eq_true, ↓reduceIte]
    have gzs := lt_swap_of e3 l3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SD]; exact c_gt_of_lt gzs)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {I : Term} {κ : Term → Term}

theorem uks2 (n : Nat) : ∀ Y L R, List.length L ≤ n → SA κ (Y :: R) → R ≠ [] → (∀ x ∈ Y :: R, (KdK I κ) x) →
    (∀ x ∈ L, (KdK I κ) x) →
    ∃ Res, Erlang.lists.«ukeysplit_2/5» I Y (κ Y) (Term.list L) (Term.list R) = .ok (Term.list Res) ∧
      SA κ Res ∧ Eqv κ Res ((Y :: R) ++ L) := by
  induction n with
  | zero =>
    intro Y L R len sr _ _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«ukeysplit_2/5».eq_def]
      exact ⟨Y :: R, by simp, sr, by simpa using Eqv.refl (Y :: R)⟩
  | succ n ih =>
  intro Y L R len sr rn kr kl
  cases L with
  | nil =>
    rw [Erlang.lists.«ukeysplit_2/5».eq_def]
    exact ⟨Y :: R, by simp, sr, by simpa using Eqv.refl (Y :: R)⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
  have len' : L.length ≤ n := by simp at len; omega
  have sr' := SA_cons.1 sr
  rw [Erlang.lists.«ukeysplit_2/5».eq_def]
  simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih Y L R len' sr rn kr kl'
    have dd := drop_at (κ := κ) (P := Y :: R) (L := L) (y := Y) (z := Z) (by simp) e1
    exact ⟨Res, run, s, er.trans dd⟩
  simp only [e1, ↓reduceIte]
  by_cases l1 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
  · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
    have rv := rev2 R []
    simp only [List.append_nil] at rv
    simp only [rv, Lynx.Except.ok_bind]
    obtain ⟨Res, run, s, er⟩ := (uks1 (I := I) (κ := κ) L.length).1 Y Z L [] [R.reverse] (by omega)
      (by simp [SD]; exact c_gt_of_lt l1)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl; exact kz; exact kr _ (by simp))
      (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact ⟨by simpa using rn, SD_reverse.2 sr'.2, fun x hx => kr x (by simp at hx; simp [hx])⟩)
      kl'
    refine ⟨Res, by simpa using run, s, er.trans ?_⟩
    -- rev R ++ [Z, Y] ++ L ≈ Y :: R ++ Z :: L
    have e2 := eqv_move (κ := κ) (A := R ++ [Z]) (B := L) (x := Y) (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl
      · rw [c_swap, sr'.1 y hy]; simp
      · intro e; exact e1 (c_eq_symm e))
    have e3 := (eqv_reverse (κ := κ) (SA.ne sr'.2)).append (Eqv.refl (Z :: Y :: L))
    simp only [List.append_assoc, List.cons_append, List.nil_append] at e2 e3 ⊢
    simpa using e3.trans e2
  have zy := lt_swap_of e1 l1
  simp only [not_islt l1, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Res, run, s, er⟩ := ih Z L (Y :: R) len' (SA_cons.2 ⟨SA.lt_all sr zy, sr⟩) (by simp)
    (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kr x (by simpa using hx))
    kl'
  have := eqv_move (κ := κ) (A := Y :: R) (B := L) (x := Z) (fun y hy => by
    have := SA.lt_all sr zy y hy; rw [c_swap, this]; simp)
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using this.symm)⟩

theorem uksort1 (n : Nat) : ∀ X L, List.length L ≤ n → (KdK I κ) X → (∀ x ∈ L, (KdK I κ) x) →
    ∃ Res, Erlang.lists.«ukeysort_1/4» I X (κ X) (Term.list L) = .ok (Term.list Res) ∧
      SA κ Res ∧ Eqv κ Res (X :: L) := by
  induction n with
  | zero =>
    intro X L len _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«ukeysort_1/4».eq_def]
      exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | succ n ih =>
  intro X L len kx kl
  cases L with
  | nil =>
    rw [Erlang.lists.«ukeysort_1/4».eq_def]
    exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, (KdK I κ) x := fun x hx => kl x (by simp [hx])
  rw [Erlang.lists.«ukeysort_1/4».eq_def]
  simp only [kz.1, Lynx.Except.ok_bind, eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih X L (by simp at len; omega) kx kl'
    exact ⟨Res, run, s, er.trans (drop_at (P := [X]) (y := X) (by simp) e1)⟩
  simp only [e1, ↓reduceIte]
  have swap : Eqv κ ([Z, X] ++ L) (X :: Z :: L) := by
    have := eqv_move (κ := κ) (A := [X]) (B := L) (x := Z) (fun y hy => by
      simp at hy; subst hy; exact e1)
    simpa using this.symm
  by_cases l1 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
  · simp only [l1, Ordering.isLT_lt, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := (uks1 (I := I) (κ := κ) L.length).1 X Z L [] [] (by omega)
      (by simp [SD]; exact c_gt_of_lt l1)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
      (by simp [RunsD]) kl'
    exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩
  have zx := lt_swap_of e1 l1
  simp only [not_islt l1, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨Res, run, s, er⟩ := uks2 (I := I) (κ := κ) L.length Z L [X] (by omega)
    (by simp [SA]; exact zx) (by simp)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
    kl'
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term}

theorem eqv_perm {A B : List Term} (p : A.Perm B)
    (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) : Eqv κ A B := by
  induction p with
  | nil => exact Eqv.refl _
  | cons x _ ih => exact Eqv.cons x (ih (List.pairwise_cons.1 h).2)
  | swap x y l =>
    have hyx : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) ≠ .eq := (List.pairwise_cons.1 h).1 x (by simp)
    have := eqv_move (κ := κ) (A := [y]) (B := l) (x := x) (by simpa using hyx)
    simpa using this
  | trans p1 _ ih1 ih2 =>
    exact (ih1 h).trans (ih2 ((p1.pairwise_iff fun e => fun e' => e (c_eq_symm e')).1 h))

end

section
variable {κ : Term → Term}

theorem and_tt : Erlang.erlang.«and/2» (.atom "true") (.atom "true") = .ok (.atom "true") := by
  simp [Erlang.erlang.«and/2»]

theorem small2 {a b : Term} (h : Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt) : SA κ [a, b] := by
  simp [SA, h]

theorem small3 {a b c : Term} (h1 : Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt) (h2 : Term.compare (Term.fuel (κ b) (κ c)) (κ b) (κ c) = .lt) :
    SA κ [a, b, c] := by
  simp [SA, h1, h2, c_lt_trans h1 h2]

/-- `lists:ukeysort/2` returns the strictly key-sorted list of the first element of each key. -/
theorem ukeysort_spec (i : Int) (hi : 0 < i) (L : List Term) (kl : ∀ x ∈ L, KdK (.integer i) κ x) :
    ∃ R, Erlang.lists.«ukeysort/2» (.integer i) (Term.list L) = .ok (Term.list R) ∧ SA κ R ∧
      Eqv κ R L := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp only [Erlang.erlang.«>/2_integers», hi, ↓reduceIte, Lynx.Except.ok_bind, Term.true, and_tt,
    Lynx.Except.guard_ok]
  match L with
  | [] => exact ⟨[], by simp, by simp, Eqv.refl _⟩
  | [x] => exact ⟨[x], by simp, by simp [SA], Eqv.refl _⟩
  | X :: Y :: T =>
  have kx := kl X (by simp)
  have ky := kl Y (by simp)
  have kt : ∀ x ∈ T, KdK (.integer i) κ x := fun x hx => kl x (by simp [hx])
  simp only [kx.1, ky.1, Lynx.Except.ok_bind, eq_ok, lt_ok, le_ok, g_if]
  by_cases e : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .eq
  · simp only [e, ↓reduceIte]
    obtain ⟨R, run, s, er⟩ := uksort1 (I := .integer i) (κ := κ) T.length X T (by omega) kx kt
    exact ⟨R, run, s, er.trans (drop_at (P := [X]) (y := X) (by simp) e)⟩
  simp only [e, ↓reduceIte]
  by_cases l : Term.compare (Term.fuel (κ X) (κ Y)) (κ X) (κ Y) = .lt
  · simp only [l, Ordering.isLT_lt, ↓reduceIte]
    match T with
    | [] => exact ⟨[X, Y], by simp, small2 l, Eqv.refl _⟩
    | [Z] =>
      have kz := (kl Z (by simp)).1
      simp only [kz, Lynx.Except.ok_bind]
      by_cases e2 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 l, drop_at (P := [X, Y]) (L := []) (y := Y) (by simp) e2⟩
      simp only [e2, ↓reduceIte]
      by_cases l2 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .lt
      · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
        exact ⟨[X, Y, Z], by simp, small3 l l2, Eqv.refl _⟩
      simp only [not_islt l2, Bool.false_eq_true, ↓reduceIte]
      have zy := lt_swap_of e2 l2
      by_cases e3 : Term.compare (Term.fuel (κ Z) (κ X)) (κ Z) (κ X) = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 l,
          drop_at (P := [X, Y]) (L := []) (y := X) (by simp) (c_eq_symm e3)⟩
      simp only [e3, ↓reduceIte]
      have e3' : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) ≠ .eq := fun h => e3 (c_eq_symm h)
      by_cases l3 : (Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z)).isLE = true
      · simp only [l3, ↓reduceIte]
        have xz := le_ne_lt l3 e3'
        have s := small3 xz zy
        exact ⟨[X, Z, Y], by simp, s, eqv_perm (.cons X (.swap Y Z [])) s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      have s := small3 (not_le_lt l3) l
      exact ⟨[Z, X, Y], by simp, s, eqv_perm (List.perm_append_singleton Z [X, Y]).symm s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (uks1 (I := .integer i) (κ := κ) (T'.length + 2)).1 X Y (Z :: W :: T') []
        [] (by simp) (by simp [SD]; exact c_gt_of_lt l)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsD]) kt
      have := eqv_move (κ := κ) (A := [Y]) (B := Z :: W :: T') (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => e (c_eq_symm h))
      exact ⟨R, by simpa using run, s, er.trans (by simpa using this)⟩
  simp only [not_islt l, Bool.false_eq_true, ↓reduceIte]
  have yx := lt_swap_of e l
  have swap : ∀ T, Eqv κ (Y :: X :: T) (X :: Y :: T) := fun T => by
    have := eqv_move (κ := κ) (A := [Y]) (B := T) (x := X)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => e (c_eq_symm h))
    simpa using this
  match T with
  | [] => exact ⟨[Y, X], by simp, small2 yx, swap []⟩
  | [Z] =>
    have kz := (kl Z (by simp)).1
    simp only [kz, Lynx.Except.ok_bind]
    by_cases e2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .eq
    · simp only [e2, ↓reduceIte]
      exact ⟨[Y, X], by simp, small2 yx,
        (swap []).trans (drop_at (P := [X, Y]) (L := []) (y := X) (by simp) e2)⟩
    simp only [e2, ↓reduceIte]
    by_cases l2 : Term.compare (Term.fuel (κ X) (κ Z)) (κ X) (κ Z) = .lt
    · simp only [l2, Ordering.isLT_lt, ↓reduceIte]
      exact ⟨[Y, X, Z], by simp, small3 yx l2, swap [Z]⟩
    simp only [not_islt l2, Bool.false_eq_true, ↓reduceIte]
    have zx := lt_swap_of e2 l2
    by_cases e3 : Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z) = .eq
    · simp only [e3, ↓reduceIte]
      exact ⟨[Y, X], by simp, small2 yx,
        (swap []).trans (drop_at (P := [X, Y]) (L := []) (y := Y) (by simp) e3)⟩
    simp only [e3, ↓reduceIte]
    by_cases l3 : (Term.compare (Term.fuel (κ Y) (κ Z)) (κ Y) (κ Z)).isLE = true
    · simp only [l3, ↓reduceIte]
      have s := small3 (le_ne_lt l3 e3) zx
      exact ⟨[Y, Z, X], by simp, s, eqv_perm (List.perm_append_singleton X [Y, Z]) s.ne⟩
    simp only [l3, Bool.false_eq_true, ↓reduceIte]
    have s := small3 (not_le_lt l3) yx
    exact ⟨[Z, Y, X], by simp, s, eqv_perm (List.reverse_perm [X, Y, Z]) s.ne⟩
  | Z :: W :: T' =>
    simp only []
    obtain ⟨R, run, s, er⟩ := uks2 (I := .integer i) (κ := κ) (T'.length + 2) Y (Z :: W :: T') [X]
      (by simp) (small2 yx) (by simp)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
      kt
    exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

/-- Elements of `usort/1` never equal a cons, the head sentinel of `umergel/3`. -/
def KdU (x : Term) : Prop := ∀ a b, Term.compare (Term.fuel x (.cons a b)) x (.cons a b) ≠ .eq

theorem um2 (n : Nat) :
    (∀ T1 T2 M H2 HdM, List.length T1 + List.length T2 + 1 ≤ n → Pre (fun x : Term => x) KdU M T1 (H2 :: T2) [] →
      HdOK (fun x : Term => x) M HdM (H2 :: T2) →
      ∃ R, Erlang.lists.«umerge2_1/5» (Term.list T1) (Term.list T2) (Term.list M) HdM H2 =
        .ok (Term.list R) ∧ Res (fun x : Term => x) M T1 (H2 :: T2) [] R) ∧
    (∀ T1 H1 T2 M, List.length T1 + 1 + List.length T2 ≤ n → Pre (fun x : Term => x) KdU M (H1 :: T1) T2 [] →
      (∀ y ∈ T2, Above (fun x : Term => x) M y) →
      ∃ R, Erlang.lists.«umerge2_2/4» (Term.list T1) (Term.list T2) (Term.list M) H1 =
        .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) T2 [] R) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ n ih =>
  constructor
  · intro T1 T2 M H2 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    cases T1 with
    | nil =>
      rw [Erlang.lists.«umerge2_1/5».eq_def]
      simp only [eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        refine ⟨_, by simp only [c2, ite_true, rev2], tr _ (res_congr (by simp) (res_fin p'.sm p'.sb ab))⟩
      · obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simp) (by simp)
        refine ⟨_, by simpa [c2] using rev2 T2 (H2 :: M), tr _ (res_congr (by simp)
          (res_fin p'.sm p'.sb fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy)))⟩
    | cons H1 T1 =>
      rw [Erlang.lists.«umerge2_1/5».eq_def]
      simp only [le_ok, eq_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1, Bool.false_eq_true, ↓reduceIte]
        have c1' := not_le_lt c1
        by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 M (by simp at len; omega) p' ab
          exact ⟨R, run, tr R res⟩
        · simp only [c2, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushB p (u2.2 c2) (by simpa using c1') (by simp)
          obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
            (fun y hy => above_cons (u2.2 c2) ((SA_cons.1 p.sb).1 y hy))
          exact ⟨R, by simpa using run, tr R res⟩
  · intro T1 H1 T2 M len p ab
    cases T2 with
    | nil =>
      rw [Erlang.lists.«umerge2_2/4».eq_def]
      obtain ⟨p', tr⟩ := pushA p (by simp) (by simp)
      refine ⟨_, by simpa using rev2 T1 (H1 :: M), tr _ (res_fin p'.sm p'.sa p'.ua)⟩
    | cons H2 T2 =>
      rw [Erlang.lists.«umerge2_2/4».eq_def]
      simp only [le_ok, g_if]
      by_cases c1 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c1, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      · simp only [c1, Bool.false_eq_true, ↓reduceIte]
        have hx := ab H2 (by simp)
        obtain ⟨p', tr⟩ := pushB p hx (by simpa using not_le_lt c1) (by simp)
        obtain ⟨R, run, res⟩ := ih.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
          (fun y hy => above_cons hx ((SA_cons.1 p.sb).1 y hy))
        exact ⟨R, by simpa using run, tr R res⟩

theorem um3 (n : Nat) :
    (∀ T1 T2 T3 M H2 H3 HdM, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M T1 (H2 :: T2) (H3 :: T3) → HdOK (fun x : Term => x) M HdM (H2 :: T2 ++ H3 :: T3) →
      ∃ R, Erlang.lists.«umerge3_1/7» (Term.list T1) HdM (Term.list T2) H2 (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ Res (fun x : Term => x) M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 T2 H3 T3 M HdM, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) T2 (H3 :: T3) → (∀ y ∈ T2, Above (fun x : Term => x) M y) → HdOK (fun x : Term => x) M HdM (H3 :: T3) →
      ∃ R, Erlang.lists.«umerge3_2/7» (Term.list T1) H1 (Term.list T2) HdM (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) T2 (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 T3 M, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y) → (∀ y ∈ T3, Above (fun x : Term => x) M y) →
      (Term.compare (Term.fuel H1 H2) H1 H2).isLE →
      ∃ R, Erlang.lists.«umerge3_12_3/6» (Term.list T1) H1 (Term.list T2) H2
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) (H2 :: T2) T3 R) ∧
    (∀ H1 T1 H2 T2 T3 M, List.length T1 + List.length T2 + List.length T3 + 2 ≤ n →
      (Pre (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) T3 → (∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y) → (∀ y ∈ T3, Above (fun x : Term => x) M y) →
      Term.compare (Term.fuel H2 H1) H2 H1 = .lt →
      ∃ R, Erlang.lists.«umerge3_21_3/6» (Term.list T1) H1 (Term.list T2) H2
        (Term.list M) (Term.list T3) = .ok (Term.list R) ∧ Res (fun x : Term => x) M (H1 :: T1) (H2 :: T2) T3 R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := um2 n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ukeymerge3_1
    intro T1 T2 T3 M H2 H3 HdM len p hd
    have u2 := up_split hd (by simp) (p.ub H2 (by simp))
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    rw [Erlang.lists.«umerge3_1/7».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 M H3 HdM (by simp at len; omega) (pre_BC p' ab)
          (hd_sub hd fun a ha => List.mem_append_right _ ha)
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simp) (by simpa using c23)
        obtain ⟨R, run, res⟩ := m2.1 T2 T3 (H2 :: M) H3 H2 (by simp at len; omega)
          (pre_BC p' (above_tail p.sb a2)) hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 M (by simp at len; omega)
          (pre_BC p' (above_all p.sb a2)) ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simp) (by simpa using c32)
      obtain ⟨R, run, res⟩ := m2.2 T2 H2 T3 (H3 :: M) (by simp at len; omega)
        (pre_BC p' (above_all p.sb (above_cons a3 c32))) (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H1 T1 =>
      have a1 := p.ua H1 (by simp)
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1 (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13, Bool.false_eq_true, ↓reduceIte]
        have c31 := not_le_lt c13
        have b2 : ∀ y ∈ H2 :: T2, Above (fun x : Term => x) M y := above_all p.sb (by
          cases e : Term.compare (Term.fuel H1 H2) H1 H2
          · exact above_lt a1 e
          · exact fun m hm => c_lt_eq (a1 m hm) e
          · simp [e] at c12)
        by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' b2 ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases c2 : Term.compare (Term.fuel H2 HdM) H2 HdM = .eq
      · simp only [c2, ↓reduceIte]
        obtain ⟨p', ab, tr⟩ := dropB p (u2.1 c2)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 M H2 (by simp at len; omega) p' ab
          (by obtain ⟨m, M', hM, hm⟩ := u2.1 c2; subst hM; exact hm)
        exact ⟨R, run, tr R res⟩
      simp only [c2, ↓reduceIte]
      have a2 := u2.2 c2
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p'
          (above_all p.sb a2) ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_2
    intro H1 T1 T2 H3 T3 M HdM len p ab hd
    have u3 := up_split hd (by simp) (p.uc H3 (by simp))
    have a1 := p.ua H1 (by simp)
    rw [Erlang.lists.«umerge3_2/7».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simp) (by simpa using c13)
        obtain ⟨R, run, res⟩ := m2.1 T1 T3 (H1 :: M) H3 H1 (by simp at len; omega) (pre_AC p') hd_self
        exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 M (by simp at len; omega) (pre_AC p') ac
        exact ⟨R, run, tr R (res_congr (by simp) res)⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T3 (H3 :: M) (by simp at len; omega) (pre_AC p')
        (above_tail p.sc a3)
      exact ⟨R, by simpa using run, tr R (res_congr (by simp) res)⟩
    | cons H2 T2 =>
      have a2 := ab H2 (by simp)
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
        · simp only [c13, ↓reduceIte]
          obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
          obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1
            (by simp at len; omega) p' hd_self
          exact ⟨R, by simpa using run, tr R res⟩
        simp only [c13, Bool.false_eq_true, ↓reduceIte]
        have c31 := not_le_lt c13
        by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
        · simp only [c3, ↓reduceIte]
          obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c12
          exact ⟨R, run, tr R res⟩
        simp only [c3, ↓reduceIte]
        have a3 := u3.2 c3
        obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
          (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2 (by simp at len; omega) p'
          (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      by_cases c3 : Term.compare (Term.fuel H3 HdM) H3 HdM = .eq
      · simp only [c3, ↓reduceIte]
        obtain ⟨p', ac, tr⟩ := dropC p (u3.1 c3)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 M (by simp at len; omega) p' ab ac c21
        exact ⟨R, run, tr R res⟩
      simp only [c3, ↓reduceIte]
      have a3 := u3.2 c3
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_12_3
    intro H1 T1 H2 T2 T3 M len p ab ac c12
    rw [Erlang.lists.«umerge3_12_3/6».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 T2 (H1 :: M) H2 H1 (by simp at len; omega) p' hd_self
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      simp only [le_ok, g_if]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushA p (by simpa using c12) (by simpa using c13)
        obtain ⟨R, run, res⟩ := ih1 T1 T2 T3 (H1 :: M) H2 H3 H1
          (by simp at len; omega) p' hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c31) (by simpa using c_lt_le c31 c12)
      obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 (c_lt_le c31 c12))) (above_tail p.sc a3) c12
      exact ⟨R, by simpa using run, tr R res⟩
  · -- ukeymerge3_21_3
    intro H1 T1 H2 T2 T3 M len p ab ac c21
    have a2 := ab H2 (by simp)
    rw [Erlang.lists.«umerge3_21_3/6».eq_def]
    cases T3 with
    | nil =>
      simp only []
      obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.2 T1 H1 T2 (H2 :: M) (by simp at len; omega) p'
        (above_tail p.sb a2)
      exact ⟨R, by simpa using run, tr R res⟩
    | cons H3 T3 =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨p', tr⟩ := pushB p a2 (by simpa using c21) (by simpa using c23)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 T2 H3 T3 (H2 :: M) H2
          (by simp at len; omega) p' (above_tail p.sb a2) hd_self
        exact ⟨R, by simpa using run, tr R res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23
      have a3 := ac H3 (by simp)
      obtain ⟨p', tr⟩ := pushC p a3 (by simpa using c_lt_trans c32 c21) (by simpa using c32)
      obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 T3 (H3 :: M) (by simp at len; omega) p'
        (above_all p.sb (above_cons a3 c32)) (above_tail p.sc a3) c21
      exact ⟨R, by simpa using run, tr R res⟩


end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem rm2 (n : Nat) :
    (∀ T1 H2 T2 M, 2 * (List.length T1 + List.length T2 + 1) + 1 ≤ n → (PreD (fun x : Term => x) KdU) M T1 (H2 :: T2) [] →
      ∃ R, Erlang.lists.«rumerge2_1/4» (Term.list T1) (Term.list T2) (Term.list M) H2 =
        .ok (Term.list R) ∧ ResD (fun x : Term => x) M T1 (H2 :: T2) [] R) ∧
    (∀ H1 T1 H2M T2 M, 2 * (List.length T1 + List.length T2 + 2) ≤ n → (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2M :: T2) [] →
      (Term.compare (Term.fuel H1 H2M) H1 H2M).isLE = true →
      ∃ R, Erlang.lists.«rumerge2_2/5» (Term.list T1) (Term.list T2) (Term.list M) H2M H1 = .ok (Term.list R) ∧ ResD (fun x : Term => x) M (H1 :: T1) (H2M :: T2) [] R) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro T1 H2 T2 M len p
    rw [Erlang.lists.«rumerge2_1/4».eq_def]
    cases T1 with
    | nil =>
      obtain ⟨p', tr⟩ := pushDB p (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T2 (H2 :: M), tr _ (resD_congr (by simp) (resD_fin p'.sm p'.sb p'.ub))⟩
    | cons H1 T1 =>
      simp only [le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 M (by simp at len; omega) p c12
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p', tr⟩ := pushDA p (by simpa using not_le_lt c12) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p'
      exact ⟨R, by simpa using run, tr R res⟩
  · intro H1 T1 H2M T2 M len p c1
    rw [Erlang.lists.«rumerge2_2/5».eq_def]
    cases T2 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
        exact ⟨_, by simpa using rev2 T1 (H1 :: M), tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simp)
      exact ⟨_, by simpa using rev2 T1 (H1 :: H2M :: M),
        tr1 _ (tr2 _ (resD_fin p2.sm p2.sa p2.ua))⟩
    | cons H2 T2 =>
      have s2 := sd_head p.sb
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simp)
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 (H2M :: M) (by simp at len; omega) p1 c12
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using le_ne_lt c1 e) (by simp)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 (H1 :: H2M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩

theorem rm3 (n : Nat) :
    (∀ T1 H2 T2 H3 T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 2) + 1 ≤ n →
      (PreD (fun x : Term => x) KdU) M T1 (H2 :: T2) (H3 :: T3) →
      ∃ R, Erlang.lists.«rumerge3_1/6» (Term.list T1) (Term.list T2) H2 (Term.list M)
        (Term.list T3) H3 = .ok (Term.list R) ∧ ResD (fun x : Term => x) M T1 (H2 :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2M T2 H3 T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2M :: T2) (H3 :: T3) → (Term.compare (Term.fuel H1 H2M) H1 H2M).isLE = true →
      Term.compare (Term.fuel H3 H2M) H3 H2M = .lt →
      ∃ R, Erlang.lists.«rumerge3_2/7» (Term.list T1) (Term.list T2) H2M
        (Term.list M) (Term.list T3) H3 H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2M :: T2) (H3 :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true →
      (Term.compare (Term.fuel H2 H3M) H2 H3M).isLE = true →
      ∃ R, Erlang.lists.«rumerge3_12_3/7» (Term.list T1) (Term.list T2) H2
        (Term.list M) (Term.list T3) H3M H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) ∧
    (∀ H1 T1 H2 T2 H3M T3 M, 2 * (List.length T1 + List.length T2 + List.length T3 + 3) ≤ n →
      (PreD (fun x : Term => x) KdU) M (H1 :: T1) (H2 :: T2) (H3M :: T3) → Term.compare (Term.fuel H2 H1) H2 H1 = .lt →
      (Term.compare (Term.fuel H1 H3M) H1 H3M).isLE = true →
      ∃ R, Erlang.lists.«rumerge3_21_3/7» (Term.list T1) (Term.list T2) H2
        (Term.list M) (Term.list T3) H3M H1 = .ok (Term.list R) ∧
        ResD (fun x : Term => x) M (H1 :: T1) (H2 :: T2) (H3M :: T3) R) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2, ih12, ih21⟩ := ih
  have m2 := rm2 n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- rukeymerge3_1
    intro T1 H2 T2 H3 T3 M len p
    rw [Erlang.lists.«rumerge3_1/6».eq_def]
    cases T1 with
    | nil =>
      simp only [le_ok, g_if]
      by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H2 T2 H3 T3 M (by simp at len; omega) (preD_BC p) c23
        exact ⟨R, run, resD_congr (by simp) res⟩
      simp only [c23, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDB p (by simp) (by simpa using not_le_lt c23)
      obtain ⟨R, run, res⟩ := m2.1 T2 H3 T3 (H2 :: M) (by simp at len; omega) (preD_BC p1)
      exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
    | cons H1 T1 =>
      simp only [le_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
        · simp only [c23, ↓reduceIte]
          exact ih12 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 c23
        simp only [c23, Bool.false_eq_true, ↓reduceIte]
        exact ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p c12 (not_le_lt c23)
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        exact ih21 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p (not_le_lt c12) c13
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p1, tr1⟩ := pushDA p (by simpa using not_le_lt c12) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p1
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_2
    intro H1 T1 H2M T2 H3 T3 M len p c1 c3
    rw [Erlang.lists.«rumerge3_2/7».eq_def]
    cases T2 with
    | nil =>
      simp only [le_ok, eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: M) (by simp at len; omega) (preD_AC p2)
        exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H3 T3 (H2M :: M) (by simp at len; omega) (preD_AC p1) c13
        exact ⟨R, by simpa using run, tr1 R (resD_congr (by simp) res)⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simp) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := m2.1 T1 H3 T3 (H1 :: H2M :: M) (by simp at len; omega) (preD_AC p2)
      exact ⟨R, by simpa using run, tr1 R (tr2 R (resD_congr (by simp) res))⟩
    | cons H2 T2 =>
      have s2 := sd_head p.sb
      simp only [le_ok, eq_ok, g_if]
      by_cases c12 : (Term.compare (Term.fuel H1 H2) H1 H2).isLE = true
      · simp only [c12, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := pushDB p (by simpa using c_le_lt c12 s2) (by simpa using c3)
        by_cases c23 : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
        · simp only [c23, ↓reduceIte]
          obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12 c23
          exact ⟨R, by simpa using run, tr1 R res⟩
        simp only [c23, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c12
          (not_le_lt c23)
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c12, Bool.false_eq_true, ↓reduceIte]
      have c21 := not_le_lt c12
      by_cases e : Term.compare (Term.fuel H1 H2M) H1 H2M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDB p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c_lt_eq c3 (c_eq_symm e))
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l12 := le_ne_lt c1 e
      obtain ⟨p1, tr1⟩ := pushDB p (by simpa using l12) (by simpa using c3)
      by_cases c13 : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13, ↓reduceIte]
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H2M :: M) (by simp at len; omega) p1 c21 c13
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using not_le_lt c13)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H2M :: M)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
  · -- rukeymerge3_12_3
    intro H1 T1 H2 T2 H3M T3 M len p c12 c23
    rw [Erlang.lists.«rumerge3_12_3/7».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H2 H3M) H2 H3M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 M (by simp at len; omega) p1 c12
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := m2.2 H1 T1 H2 T2 (H3M :: M) (by simp at len; omega) p1 c12
      exact ⟨R, by simpa using run, tr1 R res⟩
    | cons H3 T3 =>
      have s3 := sd_head p.sc
      simp only [le_ok, eq_ok, g_if]
      by_cases c23' : (Term.compare (Term.fuel H2 H3) H2 H3).isLE = true
      · simp only [c23', ↓reduceIte]
        have l23 := c_le_lt c23' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
        obtain ⟨R, run, res⟩ := ih12 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c23'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c23', Bool.false_eq_true, ↓reduceIte]
      have c32 := not_le_lt c23'
      by_cases e : Term.compare (Term.fuel H2 H3M) H2 H3M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H2) (by simp) e
        obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 M (by simp at len; omega) p1 c12 c32
        exact ⟨R, run, tr1 R res⟩
      simp only [e, ↓reduceIte]
      have l23 := le_ne_lt c23 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using c_le_lt c12 l23) (by simpa using l23)
      obtain ⟨R, run, res⟩ := ih2 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c12 c32
      exact ⟨R, by simpa using run, tr1 R res⟩
  · -- rukeymerge3_21_3
    intro H1 T1 H2 T2 H3M T3 M len p c21 c13
    rw [Erlang.lists.«rumerge3_21_3/7».eq_def]
    cases T3 with
    | nil =>
      simp only [eq_ok, g_if]
      by_cases e : Term.compare (Term.fuel H1 H3M) H1 H3M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
        obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simp)
      obtain ⟨R, run, res⟩ := m2.1 T1 H2 T2 (H1 :: H3M :: M) (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
    | cons H3 T3 =>
      have s3 := sd_head p.sc
      simp only [le_ok, eq_ok, g_if]
      by_cases c13' : (Term.compare (Term.fuel H1 H3) H1 H3).isLE = true
      · simp only [c13', ↓reduceIte]
        have l13 := c_le_lt c13' s3
        obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
        obtain ⟨R, run, res⟩ := ih21 H1 T1 H2 T2 H3 T3 (H3M :: M) (by simp at len; omega) p1 c21 c13'
        exact ⟨R, by simpa using run, tr1 R res⟩
      simp only [c13', Bool.false_eq_true, ↓reduceIte]
      have c31 := not_le_lt c13'
      by_cases e : Term.compare (Term.fuel H1 H3M) H1 H3M = .eq
      · simp only [e, ↓reduceIte]
        obtain ⟨p1, tr1⟩ := dropDC p (a := H1) (by simp) e
        obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
        obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: M) (by simp at len; omega) p2
        exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩
      simp only [e, ↓reduceIte]
      have l13 := le_ne_lt c13 e
      obtain ⟨p1, tr1⟩ := pushDC p (by simpa using l13) (by simpa using c_lt_trans c21 l13)
      obtain ⟨p2, tr2⟩ := pushDA p1 (by simpa using c21) (by simpa using c31)
      obtain ⟨R, run, res⟩ := ih1 T1 H2 T2 H3 T3 (H1 :: H3M :: M)
        (by simp at len; omega) p2
      exact ⟨R, by simpa using run, tr1 R (tr2 R res)⟩


end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable {κ : Term → Term} {Kd : Term → Prop}

theorem pre_nil {A B C : List Term} (sa : SA κ A) (sb : SA κ B) (sc : SA κ C) (ka : ∀ x ∈ A, Kd x)
    (kb : ∀ x ∈ B, Kd x) (kc : ∀ x ∈ C, Kd x) : Pre κ Kd [] A B C :=
  ⟨SD_nil, sa, sb, sc, ka, kb, kc, fun _ _ _ h => by simp at h,
    fun _ _ => Or.inl fun _ h => by simp at h, fun _ _ => Or.inl fun _ h => by simp at h⟩

theorem preD_nil {A B C : List Term} (sa : SD κ A) (sb : SD κ B) (sc : SD κ C) (ka : ∀ x ∈ A, Kd x)
    (kb : ∀ x ∈ B, Kd x) (kc : ∀ x ∈ C, Kd x) : PreD κ Kd [] A B C :=
  ⟨SA_nil, sa, sb, sc, ka, kb, kc, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h,
    fun _ _ _ h => by simp at h⟩

/-- A merge of nonempty keyed sources from an empty accumulator is a descending run. -/
theorem run_of_res {A B C R : List Term} (r : Res κ [] A B C R) (ne : A ++ B ++ C ≠ [])
    (k : ∀ x ∈ A ++ B ++ C, Kd x) : R ≠ [] ∧ SD κ R ∧ ∀ x ∈ R, Kd x :=
  ⟨eqv_ne_nil r.2 (by simpa using ne), r.1, kd_of_eqv r.1.ne r.2 (by simpa using k)⟩

theorem run_of_resD {A B C R : List Term} (r : ResD κ [] A B C R) (ne : A ++ B ++ C ≠ [])
    (k : ∀ x ∈ A ++ B ++ C, Kd x) : R ≠ [] ∧ SA κ R ∧ ∀ x ∈ R, Kd x :=
  ⟨eqv_ne_nil r.2 (by simpa using ne), r.1, kd_of_eqv r.1.ne r.2 (by simpa using k)⟩

theorem runsA_cons {r : List Term} {Rs : List (List Term)} (h : r ≠ [] ∧ SA κ r ∧ ∀ x ∈ r, Kd x)
    (hs : RunsA (κ := κ) Kd Rs) : RunsA (κ := κ) Kd (r :: Rs) := by
  intro r' hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr; exact h; exact hs r' hr

theorem runsD_cons {r : List Term} {Rs : List (List Term)} (h : r ≠ [] ∧ SD κ r ∧ ∀ x ∈ r, Kd x)
    (hs : RunsD (κ := κ) Kd Rs) : RunsD (κ := κ) Kd (r :: Rs) := by
  intro r' hr; simp only [List.mem_cons] at hr; rcases hr with rfl | hr; exact h; exact hs r' hr

end

/-- The run order of `umergel/3` and `rumergel/3`. -/
def modeT (asc : Bool) : Term := if asc then .atom "asc" else .atom "desc"

/-- Contents of a `umergel/3` state: in ascending mode runs come oldest first and the
accumulator newest first; in descending mode the other way around. -/
def ucontent (asc : Bool) (Rs Acc : List (List Term)) : List Term :=
  if asc then Acc.reverse.flatten ++ Rs.flatten else Rs.reverse.flatten ++ Acc.flatten

def rcontent (asc : Bool) (Rs Acc : List (List Term)) : List Term :=
  if asc then Rs.reverse.flatten ++ Acc.flatten else Acc.reverse.flatten ++ Rs.flatten

theorem kdu_cons {S : List Term} {a b : Term} (k : ∀ x ∈ S, KdU x) :
    ∀ x ∈ S, Term.compare (Term.fuel ((fun x : Term => x) x) (.cons a b)) ((fun x : Term => x) x) (.cons a b) ≠ .eq := fun x hx => k x hx a b

theorem um_mergel (n : Nat) :
    (∀ asc Rs Acc, 4 * (List.length Rs + List.length Acc) + 2 * min (List.length Acc) 1 ≤ n →
      1 ≤ List.length Rs + List.length Acc → RunsA (κ := (fun x : Term => x)) KdU Rs → RunsD (κ := (fun x : Term => x)) KdU Acc →
      ∃ R, Erlang.lists.«umergel/3» (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list))
        (modeT asc) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R (ucontent asc Rs Acc)) ∧
    (∀ asc Rs Acc, 4 * (List.length Rs + List.length Acc) + 2 * min (List.length Acc) 1 + 1 ≤ n →
      1 ≤ List.length Rs + List.length Acc → RunsD (κ := (fun x : Term => x)) KdU Rs → RunsA (κ := (fun x : Term => x)) KdU Acc →
      ∃ R, Erlang.lists.«rumergel/3» (Term.list (Rs.map Term.list)) (Term.list (Acc.map Term.list))
        (modeT asc) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R (rcontent asc Rs Acc)) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> intros <;> omega
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro asc Rs Acc len one ra rd
    rw [Erlang.lists.«umergel/3».eq_def]
    match Rs with
    | [] =>
      cases Acc with
      | nil => simp at one
      | cons A Acc =>
      obtain ⟨na, _, _⟩ := rd A (by simp)
      obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil na
      simp only [List.map_nil, List.map_cons]
      obtain ⟨R, run, sr, er⟩ := ih2 asc ((a :: A') :: Acc) [] (by simp at len ⊢; omega) (by simp) rd
        (by simp [RunsA])
      refine ⟨R, by simpa using run, sr, ?_⟩
      cases asc <;> simpa [ucontent, rcontent] using er
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := ra L (by simp)
      obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil nl
      cases Acc with
      | nil =>
        refine ⟨h :: t, by simp, sl, ?_⟩
        cases asc <;> simpa [ucontent] using Eqv.refl (κ := (fun x : Term => x)) (h :: t)
      | cons A Acc =>
        obtain ⟨na, _, _⟩ := rd A (by simp)
        obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil na
        have rv := rev2 (h :: t) []
        simp only [List.append_nil] at rv
        simp only [List.map_nil, List.map_cons]
        simp only [← Term.list_cons, rv, Lynx.Except.ok_bind]
        obtain ⟨R, run, sr, er⟩ := ih2 asc ((h :: t).reverse :: (a :: A') :: Acc) []
          (by simp at len ⊢; omega) (by simp)
          (runsD_cons ⟨by simp, SD_reverse.2 sl, fun x hx => kl x (List.mem_reverse.1 hx)⟩ rd)
          (by simp [RunsA])
        refine ⟨R, by simpa using run, sr, er.trans ?_⟩
        have rv' := eqv_reverse (κ := (fun x : Term => x)) sl.ne
        rw [List.reverse_cons] at rv'
        cases asc
        · simp only [rcontent, ucontent, Bool.false_eq_true, ↓reduceIte, List.reverse_nil,
            List.flatten_nil, List.nil_append, List.flatten_cons, List.reverse_cons,
            List.append_nil]
          exact Eqv.append rv' (Eqv.refl _)
        · simp only [rcontent, ucontent, ↓reduceIte, List.reverse_cons, List.flatten_append,
            List.flatten_cons, List.flatten_nil, List.append_nil,
            List.append_assoc]
          exact Eqv.append (Eqv.refl _) (Eqv.append (Eqv.refl _) rv')
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (um2 (t2.length + 1 + (h1 :: t1).length)).2 t2 h2 (h1 :: t1) [] (by simp)
          (pre_nil s2 s1 SA_nil k2 k1 (by simp)) (fun _ _ _ h => by simp at h)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 false [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsA]) (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc [] Acc.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (um2 (t1.length + 1 + (h2 :: t2).length)).2 t1 h1 (h2 :: t2) [] (by simp)
          (pre_nil s1 s2 SA_nil k1 k2 (by simp)) (fun _ _ _ h => by simp at h)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 true [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsA]) (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten [] (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨n1, s1, k1⟩ := ra r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := ra r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := ra r3 (by simp)
      have rl : RunsA (κ := (fun x : Term => x)) KdU L := fun r hr => ra r (by simp [hr])
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨h3, t3, rfl⟩ := List.exists_cons_of_ne_nil n3
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (um3 ((h3 :: t3).length + t2.length + t1.length + 2)).1 (h3 :: t3) t2 t1 []
          h2 h1 (.cons h2 h1) (by simp) (pre_nil s3 s2 s1 k3 k2 k1) (by
            intro x hx; simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
            rcases hx with rfl | hx | rfl | hx
            · exact k2 _ (by simp) _ _
            · exact k2 x (by simp [hx]) _ _
            · exact k1 _ (by simp) _ _
            · exact k1 x (by simp [hx]) _ _)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k3 x hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 false L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc L.reverse.flatten Acc.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (um3 ((h1 :: t1).length + t2.length + t3.length + 2)).1 (h1 :: t1) t2 t3 []
          h2 h3 (.cons h2 h3) (by simp) (pre_nil s1 s2 s3 k1 k2 k3) (by
            intro x hx; simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
            rcases hx with rfl | hx | rfl | hx
            · exact k2 _ (by simp) _ _
            · exact k2 x (by simp [hx]) _ _
            · exact k3 _ (by simp) _ _
            · exact k3 x (by simp [hx]) _ _)
        obtain ⟨mn, sm, km⟩ := run_of_res res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k1 x hx; exact k2 x hx; exact k3 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih1 true L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsD_cons ⟨mn, sm, km⟩ rd)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten L.flatten (by simpa [ucontent] using er) res.2
        simpa [ucontent] using this
  · intro asc Rs Acc len one rd ra
    rw [Erlang.lists.«rumergel/3».eq_def]
    match Rs with
    | [] =>
      simp only [List.map_nil]
      obtain ⟨R, run, sr, er⟩ := ih1 asc Acc [] (by simp at len one ⊢; omega) (by simpa using one) ra
        (by simp [RunsD])
      refine ⟨R, run, sr, ?_⟩
      cases asc <;> simpa [ucontent, rcontent] using er
    | [L] =>
      obtain ⟨nl, sl, kl⟩ := rd L (by simp)
      obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil nl
      have rv := rev2 (h :: t) []
      simp only [List.append_nil] at rv
      simp only [List.map_nil, List.map_cons]
      simp only [← Term.list_cons, rv, Lynx.Except.ok_bind]
      obtain ⟨R, run, sr, er⟩ := ih1 asc ((h :: t).reverse :: Acc) [] (by simp at len ⊢; omega) (by simp)
        (runsA_cons ⟨by simp, SA_reverse.2 sl, fun x hx => kl x (List.mem_reverse.1 hx)⟩ ra)
        (by simp [RunsD])
      refine ⟨R, by simpa using run, sr, er.trans ?_⟩
      have rv' := eqv_reverse (κ := (fun x : Term => x)) sl.ne
      rw [List.reverse_cons] at rv'
      cases asc
      · simp only [rcontent, ucontent, Bool.false_eq_true, ↓reduceIte, List.reverse_cons,
          List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        exact Eqv.append (Eqv.refl _) rv'
      · simp only [rcontent, ucontent, ↓reduceIte, List.reverse_nil, List.flatten_nil, List.nil_append,
          List.flatten_cons, List.reverse_cons,
          List.append_nil]
        exact Eqv.append rv' (Eqv.refl _)
    | [r1, r2] =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (rm2 (2 * ((h1 :: t1).length + t2.length + 1) + 1)).1 (h1 :: t1) h2 t2 []
          (by simp) (preD_nil s1 s2 SD_nil k1 k2 (by simp))
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k1 x hx; exact k2 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 false [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsD]) (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten [] (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons, List.map_nil]
        obtain ⟨M, run, res⟩ := (rm2 (2 * ((h2 :: t2).length + t1.length + 1) + 1)).1 (h2 :: t2) h1 t1 []
          (by simp) (preD_nil s2 s1 SD_nil k2 k1 (by simp))
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.append_nil, List.mem_append] at hx
          rcases hx with hx | hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 true [] (M :: Acc) (by simp at len ⊢; omega) (by simp)
          (by simp [RunsD]) (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc [] Acc.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
    | r1 :: r2 :: r3 :: L =>
      obtain ⟨n1, s1, k1⟩ := rd r1 (by simp)
      obtain ⟨n2, s2, k2⟩ := rd r2 (by simp)
      obtain ⟨n3, s3, k3⟩ := rd r3 (by simp)
      have rl : RunsD (κ := (fun x : Term => x)) KdU L := fun r hr => rd r (by simp [hr])
      obtain ⟨h1, t1, rfl⟩ := List.exists_cons_of_ne_nil n1
      obtain ⟨h2, t2, rfl⟩ := List.exists_cons_of_ne_nil n2
      obtain ⟨h3, t3, rfl⟩ := List.exists_cons_of_ne_nil n3
      cases asc
      · simp only [modeT, Bool.false_eq_true, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (rm3 (2 * ((h1 :: t1).length + t2.length + t3.length + 2) + 1)).1
          (h1 :: t1) h2 t2 h3 t3 [] (by simp) (preD_nil s1 s2 s3 k1 k2 k3)
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k1 x hx; exact k2 x hx; exact k3 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 false L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc Acc.reverse.flatten L.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this
      · simp only [modeT, ↓reduceIte, List.map_cons]
        obtain ⟨M, run, res⟩ := (rm3 (2 * ((h3 :: t3).length + t2.length + t1.length + 2) + 1)).1
          (h3 :: t3) h2 t2 h1 t1 [] (by simp) (preD_nil s3 s2 s1 k3 k2 k1)
        obtain ⟨mn, sm, km⟩ := run_of_resD res (by simp) (by
          intro x hx; simp only [List.mem_append] at hx
          rcases hx with (hx | hx) | hx; exact k3 x hx; exact k2 x hx; exact k1 x hx)
        simp only [← Term.list_cons, run, Lynx.Except.ok_bind]
        obtain ⟨R, run', sr, er⟩ := ih2 true L (M :: Acc) (by simp at len ⊢; omega)
          (by simp only [List.length_cons]; omega) rl (runsA_cons ⟨mn, sm, km⟩ ra)
        refine ⟨R, by simpa [modeT] using run', sr, ?_⟩
        have := eqv_acc L.reverse.flatten Acc.flatten (by simpa [rcontent] using er) res.2
        simpa [rcontent] using this

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem isgt_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isGT = true) : Term.compare (Term.fuel b a) b a = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all [c_lt_of_gt]

theorem not_isgt {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isGT = true) : Term.compare (Term.fuel a b) a b ≠ .gt := by
  intro e; simp [e] at h

theorem lt_of_ne {a b : Term} (g : Term.compare (Term.fuel a b) a b ≠ .gt) (e : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel a b) a b = .lt := by
  cases h : Term.compare (Term.fuel a b) a b <;> simp_all

theorem islt_lt {a b : Term} (h : (Term.compare (Term.fuel a b) a b).isLT = true) : Term.compare (Term.fuel a b) a b = .lt := by
  cases e : Term.compare (Term.fuel a b) a b <;> simp_all

theorem not_islt' {a b : Term} (h : ¬(Term.compare (Term.fuel a b) a b).isLT = true) : Term.compare (Term.fuel a b) a b ≠ .lt := by
  intro e; simp [e] at h

theorem gt_of_ne {a b : Term} (l : Term.compare (Term.fuel a b) a b ≠ .lt) (e : ¬Term.compare (Term.fuel a b) a b = .eq) :
    Term.compare (Term.fuel b a) b a = .lt := by
  cases h : Term.compare (Term.fuel a b) a b
  · exact absurd h l
  · exact absurd h e
  · exact c_lt_of_gt h

theorem us1_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SD (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (rs : RunsD (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_1/5» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«usplit_1/5».eq_def]
  cases R <;>
  · obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 2) + 1)).2 true
      ((Y :: X :: _) :: Rs) [] (by simp; omega) (by simp) (runsD_cons ⟨by simp, sc, kc⟩ rs)
      (by simp [RunsA])
    exact ⟨Res, by simpa [modeT] using run, sr, by simpa [rcontent] using er⟩

theorem us11_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SD (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (ks : KdU S) (rs : RunsD (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_1_1/6» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«usplit_1_1/6».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 3) + 1)).2 true
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp)
    (runsD_cons ⟨by simp, by simp [SD], by simpa using ks⟩ (runsD_cons ⟨by simp, sc, kc⟩ rs))
    (by simp [RunsA])
  exact ⟨Res, by simpa [modeT] using run, sr, by simpa [rcontent] using er⟩

theorem us1 (n : Nat) :
    (∀ X Y L R Rs, List.length L ≤ n → SD (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      RunsD (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_1/5» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, List.length L ≤ n → SD (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      Term.compare (Term.fuel S X) S X = .lt → KdU S → RunsD (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_1_1/6» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact us1_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact us11_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact us1_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel X Y) X Y = .lt := c_lt_of_gt (sc'.1 X (by simp))
    rw [Erlang.lists.«usplit_1/5».eq_def]
    simp only [eq_ok, gt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isGT = true
    · simp only [g1, ↓reduceIte]
      have l1 := isgt_lt g1
      have gz := SD.gt_all (κ := (fun x : Term => x)) sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := gz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have gzy := lt_of_ne (not_isgt g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isGT = true
    · simp only [g2, ↓reduceIte]
      have l2 := isgt_lt g2
      have gzx := SD.gt_all (κ := (fun x : Term => x)) sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih1 Z Y L (X :: R) Rs len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
          rcases hy with rfl | hy
          · intro e; exact zy (c_eq_symm e)
          · have := gzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have gzx := lt_of_ne (not_isgt g2) e2
    cases R with
    | nil =>
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L [Z] Rs len'
        (by simp [SD]; exact ⟨⟨sc'.1 X (by simp), c_gt_of_lt (c_lt_trans gzx yx)⟩, c_gt_of_lt gzx⟩)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact kc x (by simp)
          · exact kc x (by simp)
          · exact kz)
        rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
    | cons r R =>
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc gzx kz rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc sx ks rs kl
    cases L with
    | nil => exact us11_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SD_cons.1 sc
    have yx : Term.compare (Term.fuel X Y) X Y = .lt := c_lt_of_gt (sc'.1 X (by simp))
    have sy := c_lt_trans sx yx
    rw [Erlang.lists.«usplit_1_1/6».eq_def]
    simp only [eq_ok, gt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isGT = true
    · simp only [g1, ↓reduceIte]
      have l1 := isgt_lt g1
      have gz := SD.gt_all (κ := (fun x : Term => x)) sc (c_gt_of_lt l1)
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SD_cons.2 ⟨gz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        sy ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | rfl
          · have := gz y (by simpa using hy); rw [c_swap, this]; simp
          · rw [c_lt_trans sy l1]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have gzy := lt_of_ne (not_isgt g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isGT = true
    · simp only [g2, ↓reduceIte]
      have l2 := isgt_lt g2
      have gzx := SD.gt_all (κ := (fun x : Term => x)) sc'.2 (c_gt_of_lt l2)
      obtain ⟨Res, run, sr, er⟩ := ih2 Z Y L (X :: R) Rs S len'
        (SD_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact c_gt_of_lt gzy
            · exact sc'.1 w (by simpa using hw), SD_cons.2 ⟨gzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        (c_lt_trans sx l2) ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, gzx _ (by simp)]; simp
          · rw [c_swap, gzx y (by simp [hy])]; simp
          · rw [c_lt_trans sx l2]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have rs' : RunsD (κ := (fun x : Term => x)) KdU ((Y :: X :: R) :: Rs) := runsD_cons ⟨by simp, sc, kc⟩ rs
    by_cases g3 : (Term.compare (Term.fuel Z S) Z S).isGT = true
    · simp only [g3, ↓reduceIte]
      have l3 := isgt_lt g3
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SD]; exact c_gt_of_lt l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; rw [l3]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g3, Bool.false_eq_true, ↓reduceIte]
    by_cases e3 : Term.compare (Term.fuel Z S) Z S = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc sx ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) (c_eq_symm e3)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    have gzs := lt_of_ne (not_isgt g3) e3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SD]; exact c_gt_of_lt gzs)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem us2_end (X Y : Term) (R : List Term) (Rs : List (List Term)) (sc : SA (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (rs : RunsA (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_2/5» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ []) := by
  rw [Erlang.lists.«usplit_2/5».eq_def]
  cases R <;>
  · obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 2))).1 false
      ((Y :: X :: _) :: Rs) [] (by simp; omega) (by simp) (runsA_cons ⟨by simp, sc, kc⟩ rs)
      (by simp [RunsD])
    exact ⟨Res, by simpa [modeT] using run, sr, by simpa [ucontent] using er⟩

theorem us21_end (X Y S : Term) (R : List Term) (Rs : List (List Term)) (sc : SA (fun x : Term => x) (Y :: X :: R))
    (kc : ∀ x ∈ Y :: X :: R, KdU x) (ks : KdU S) (rs : RunsA (κ := (fun x : Term => x)) KdU Rs) :
    ∃ Res, Erlang.lists.«usplit_2_1/6» X Y (Term.list []) (Term.list R)
      (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
      Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ [S]) := by
  rw [Erlang.lists.«usplit_2_1/6».eq_def]
  obtain ⟨Res, run, sr, er⟩ := (um_mergel (4 * (Rs.length + 3))).1 false
    ([S] :: (Y :: X :: R) :: Rs) [] (by simp; omega) (by simp)
    (runsA_cons ⟨by simp, by simp [SA], by simpa using ks⟩ (runsA_cons ⟨by simp, sc, kc⟩ rs))
    (by simp [RunsD])
  exact ⟨Res, by simpa [modeT] using run, sr, by simpa [ucontent] using er⟩

theorem us2 (n : Nat) :
    (∀ X Y L R Rs, List.length L ≤ n → SA (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      RunsA (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_2/5» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ L)) ∧
    (∀ X Y L R Rs S, List.length L ≤ n → SA (fun x : Term => x) (Y :: X :: R) → (∀ x ∈ Y :: X :: R, KdU x) →
      Term.compare (Term.fuel X S) X S = .lt → KdU S → RunsA (κ := (fun x : Term => x)) KdU Rs → (∀ x ∈ L, KdU x) →
      ∃ Res, Erlang.lists.«usplit_2_1/6» X Y (Term.list L) (Term.list R)
        (Term.list (Rs.map Term.list)) S = .ok (Term.list Res) ∧ SA (fun x : Term => x) Res ∧
        Eqv (fun x : Term => x) Res (Rs.reverse.flatten ++ (Y :: X :: R) ++ S :: L)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro X Y L R Rs len sc kc rs _
      cases L with
      | cons => simp at len
      | nil => exact us2_end X Y R Rs sc kc rs
    · intro X Y L R Rs S len sc kc _ ks rs _
      cases L with
      | cons => simp at len
      | nil => exact us21_end X Y S R Rs sc kc ks rs
  | succ n ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨?_, ?_⟩
  · intro X Y L R Rs len sc kc rs kl
    cases L with
    | nil => exact us2_end X Y R Rs sc kc rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SA_cons.1 sc
    have yx : Term.compare (Term.fuel Y X) Y X = .lt := sc'.1 X (by simp)
    rw [Erlang.lists.«usplit_2/5».eq_def]
    simp only [eq_ok, lt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
    · simp only [g1, ↓reduceIte]
      have l1 := islt_lt g1
      have lz := SA.lt_all (κ := (fun x : Term => x)) sc l1
      obtain ⟨Res, run, sr, er⟩ := ih1 Y Z L (X :: R) Rs len' (SA_cons.2 ⟨lz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R) (L := L) (z := Z)
        (fun y hy => by have := lz y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := Y) (z := Z)
        (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have yz := gt_of_ne (not_islt' g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isLT = true
    · simp only [g2, ↓reduceIte]
      have l2 := islt_lt g2
      have lzx := SA.lt_all (κ := (fun x : Term => x)) sc'.2 l2
      obtain ⟨Res, run, sr, er⟩ := ih1 Z Y L (X :: R) Rs len'
        (SA_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact yz
            · exact sc'.1 w (by simpa using hw), SA_cons.2 ⟨lzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
          rcases hy with rfl | hy
          · intro e; exact zy (c_eq_symm e)
          · have := lzx y (by simpa using hy); rw [c_swap, this]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L R Rs len' sc kc rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (L := L) (y := X) (z := Z)
        (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have xz := gt_of_ne (not_islt' g2) e2
    cases R with
    | nil =>
      obtain ⟨Res, run, sr, er⟩ := ih1 X Y L [Z] Rs len'
        (by simp [SA]; exact ⟨⟨yx, c_lt_trans yx xz⟩, xz⟩)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact kc x (by simp)
          · exact kc x (by simp)
          · exact kz)
        rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
    | cons r R =>
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L (r :: R) Rs Z len' sc kc xz kz rs kl'
      exact ⟨Res, by simpa using run, sr, by simpa using er⟩
  · intro X Y L R Rs S len sc kc xs ks rs kl
    cases L with
    | nil => exact us21_end X Y S R Rs sc kc ks rs
    | cons Z L =>
    have kz := kl Z (by simp)
    have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
    have len' : L.length ≤ n := by simp at len; omega
    have sc' := SA_cons.1 sc
    have yx : Term.compare (Term.fuel Y X) Y X = .lt := sc'.1 X (by simp)
    have ys := c_lt_trans yx xs
    rw [Erlang.lists.«usplit_2_1/6».eq_def]
    simp only [eq_ok, lt_ok, g_if]
    by_cases g1 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
    · simp only [g1, ↓reduceIte]
      have l1 := islt_lt g1
      have lz := SA.lt_all (κ := (fun x : Term => x)) sc l1
      obtain ⟨Res, run, sr, er⟩ := ih2 Y Z L (X :: R) Rs S len' (SA_cons.2 ⟨lz, sc⟩)
        (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact kz; exact kc x (by simpa using hx))
        ys ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := []) (B := Y :: X :: R ++ [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | rfl
          · have := lz y (by simpa using hy); rw [c_swap, this]; simp
          · rw [c_swap, c_lt_trans l1 ys]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g1, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : Term.compare (Term.fuel Z Y) Z Y = .eq
    · simp only [e1, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := Y)
        (z := Z) (by simp) (c_eq_symm e1)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e1, ↓reduceIte]
    have yz := gt_of_ne (not_islt' g1) e1
    have zy : Term.compare (Term.fuel Z Y) Z Y ≠ .eq := e1
    by_cases g2 : (Term.compare (Term.fuel Z X) Z X).isLT = true
    · simp only [g2, ↓reduceIte]
      have l2 := islt_lt g2
      have lzx := SA.lt_all (κ := (fun x : Term => x)) sc'.2 l2
      obtain ⟨Res, run, sr, er⟩ := ih2 Z Y L (X :: R) Rs S len'
        (SA_cons.2 ⟨fun w hw => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact yz
            · exact sc'.1 w (by simpa using hw), SA_cons.2 ⟨lzx, sc'.2⟩⟩)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact kc x (by simp)
          · exact kz
          · exact kc x (by simp [hx]))
        (c_lt_trans l2 xs) ks rs kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten) (A := [Y]) (B := X :: R ++ [S]) (L := L) (z := Z)
        (fun y hy => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | hy | rfl
          · intro e; exact zy (c_eq_symm e)
          · rw [c_swap, lzx _ (by simp)]; simp
          · rw [c_swap, lzx y (by simp [hy])]; simp
          · rw [c_swap, c_lt_trans l2 xs]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g2, Bool.false_eq_true, ↓reduceIte]
    by_cases e2 : Term.compare (Term.fuel Z X) Z X = .eq
    · simp only [e2, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := X)
        (z := Z) (by simp) (c_eq_symm e2)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e2, ↓reduceIte]
    have rs' : RunsA (κ := (fun x : Term => x)) KdU ((Y :: X :: R) :: Rs) := runsA_cons ⟨by simp, sc, kc⟩ rs
    by_cases g3 : (Term.compare (Term.fuel Z S) Z S).isLT = true
    · simp only [g3, ↓reduceIte]
      have l3 := islt_lt g3
      obtain ⟨Res, run, sr, er⟩ := ih1 S Z L [] ((Y :: X :: R) :: Rs) len'
        (by simp [SA]; exact l3)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact ks)
        rs' kl'
      have := ins_mid (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R) (A := []) (B := [S]) (L := L)
        (z := Z) (fun y hy => by
          simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; rw [c_swap, l3]; simp)
      exact ⟨Res, by simpa using run, sr, er.trans (by simpa using this)⟩
    simp only [g3, Bool.false_eq_true, ↓reduceIte]
    by_cases e3 : Term.compare (Term.fuel Z S) Z S = .eq
    · simp only [e3, ↓reduceIte]
      obtain ⟨Res, run, sr, er⟩ := ih2 X Y L R Rs S len' sc kc xs ks rs kl'
      have dd := drop_at (κ := (fun x : Term => x)) (P := Rs.reverse.flatten ++ Y :: X :: R ++ [S]) (L := L) (y := S)
        (z := Z) (by simp) (c_eq_symm e3)
      exact ⟨Res, run, sr, er.trans (by simpa using dd)⟩
    simp only [e3, ↓reduceIte]
    have sz := gt_of_ne (not_islt' g3) e3
    obtain ⟨Res, run, sr, er⟩ := ih1 Z S L [] ((Y :: X :: R) :: Rs) len'
      (by simp [SA]; exact sz)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ks; exact kz)
      rs' kl'
    exact ⟨Res, by simpa using run, sr, by simpa using er⟩

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.USort
open Lynx

theorem usort1 (n : Nat) : ∀ X L, List.length L ≤ n → KdU X → (∀ x ∈ L, KdU x) →
    ∃ Res, Erlang.lists.«usort_1/2» X (Term.list L) = .ok (Term.list Res) ∧
      SA (fun x : Term => x) Res ∧ Eqv (fun x : Term => x) Res (X :: L) := by
  induction n with
  | zero =>
    intro X L len _ _
    cases L with
    | cons => simp at len
    | nil =>
      rw [Erlang.lists.«usort_1/2».eq_def]
      exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | succ n ih =>
  intro X L len kx kl
  cases L with
  | nil =>
    rw [Erlang.lists.«usort_1/2».eq_def]
    exact ⟨[X], by simp, by simp [SA], Eqv.refl _⟩
  | cons Z L =>
  have kz := kl Z (by simp)
  have kl' : ∀ x ∈ L, KdU x := fun x hx => kl x (by simp [hx])
  rw [Erlang.lists.«usort_1/2».eq_def]
  simp only [eq_ok, lt_ok, g_if]
  by_cases e1 : Term.compare (Term.fuel X Z) X Z = .eq
  · simp only [e1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := ih X L (by simp at len; omega) kx kl'
    exact ⟨Res, run, s, er.trans (drop_at (κ := (fun x : Term => x)) (P := [X]) (y := X) (by simp) e1)⟩
  simp only [e1, ↓reduceIte]
  have swap : Eqv (fun x : Term => x) ([Z, X] ++ L) (X :: Z :: L) := by
    have := eqv_move (κ := (fun x : Term => x)) (A := [X]) (B := L) (x := Z) (fun y hy => by
      simp at hy; subst hy; exact e1)
    simpa using this.symm
  by_cases l1 : (Term.compare (Term.fuel X Z) X Z).isLT = true
  · simp only [l1, ↓reduceIte]
    obtain ⟨Res, run, s, er⟩ := (us1 L.length).1 X Z L [] [] (by omega)
      (by simp [SD]; exact c_gt_of_lt (islt_lt l1))
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
      (by simp [RunsD]) kl'
    exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩
  simp only [l1, Bool.false_eq_true, ↓reduceIte]
  have zx := gt_of_ne (not_islt' l1) e1
  obtain ⟨Res, run, s, er⟩ := (us2 L.length).1 X Z L [] [] (by omega)
    (by simp [SA]; exact zx)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact kz; exact kx)
    (by simp [RunsA]) kl'
  exact ⟨Res, by simpa using run, s, er.trans (by simpa using swap)⟩

/-- `lists:usort/1` returns the strictly sorted list of the first element of each class of equal
terms, for terms that never compare equal to a cons cell. -/
theorem usort_spec (L : List Term) (kl : ∀ x ∈ L, KdU x) :
    ∃ R, Erlang.lists.«usort/1» (Term.list L) = .ok (Term.list R) ∧ SA (fun x : Term => x) R ∧ Eqv (fun x : Term => x) R L := by
  rw [Erlang.lists.«usort/1».eq_def]
  match L with
  | [] => exact ⟨[], by simp, by simp, Eqv.refl _⟩
  | [x] => exact ⟨[x], by simp, by simp [SA], Eqv.refl _⟩
  | X :: Y :: T =>
  have kx := kl X (by simp)
  have ky := kl Y (by simp)
  have kt : ∀ x ∈ T, KdU x := fun x hx => kl x (by simp [hx])
  simp only [lt_ok, gt_ok, eq_ok, g_if]
  by_cases l : (Term.compare (Term.fuel X Y) X Y).isLT = true
  · simp only [l, ↓reduceIte]
    have xy := islt_lt l
    have xy' : Term.compare (Term.fuel X Y) X Y ≠ .eq := by simp [xy]
    have swap : ∀ T, Eqv (fun x : Term => x) (Y :: X :: T) (X :: Y :: T) := fun T => by
      have := eqv_move (κ := (fun x : Term => x)) (A := [Y]) (B := T) (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => xy' (c_eq_symm h))
      simpa using this
    match T with
    | [] => exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy, Eqv.refl _⟩
    | [Z] =>
      simp only []
      by_cases l2 : (Term.compare (Term.fuel Y Z) Y Z).isLT = true
      · simp only [l2, ↓reduceIte]
        exact ⟨[X, Y, Z], by simp, small3 xy (islt_lt l2), Eqv.refl _⟩
      simp only [l2, Bool.false_eq_true, ↓reduceIte]
      by_cases e2 : Term.compare (Term.fuel Y Z) Y Z = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy, drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := Y) (by simp) e2⟩
      simp only [e2, ↓reduceIte]
      have zy := gt_of_ne (not_islt' l2) e2
      by_cases l3 : (Term.compare (Term.fuel Z X) Z X).isLT = true
      · simp only [l3, ↓reduceIte]
        have s := small3 (κ := (fun x : Term => x)) (islt_lt l3) xy
        exact ⟨[Z, X, Y], by simp, s, eqv_perm (List.perm_append_singleton Z [X, Y]).symm s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      by_cases e3 : Term.compare (Term.fuel Z X) Z X = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[X, Y], by simp, small2 (κ := (fun x : Term => x)) xy,
          drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := X) (by simp) (c_eq_symm e3)⟩
      simp only [e3, ↓reduceIte]
      have s := small3 (κ := (fun x : Term => x)) (gt_of_ne (not_islt' l3) e3) zy
      exact ⟨[X, Z, Y], by simp, s, eqv_perm (.cons X (.swap Y Z [])) s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (us1 (T'.length + 2)).1 X Y (Z :: W :: T') [] [] (by simp)
        (by simp [SD]; exact c_gt_of_lt xy)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsD]) kt
      exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩
  simp only [l, Bool.false_eq_true, ↓reduceIte]
  by_cases g : (Term.compare (Term.fuel X Y) X Y).isGT = true
  · simp only [g, ↓reduceIte]
    have yx := isgt_lt g
    have xy' : Term.compare (Term.fuel X Y) X Y ≠ .eq := by intro e; simp [e] at g
    have swap : ∀ T, Eqv (fun x : Term => x) (Y :: X :: T) (X :: Y :: T) := fun T => by
      have := eqv_move (κ := (fun x : Term => x)) (A := [Y]) (B := T) (x := X)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact fun h => xy' (c_eq_symm h))
      simpa using this
    match T with
    | [] => exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx, swap []⟩
    | [Z] =>
      simp only []
      by_cases l2 : (Term.compare (Term.fuel X Z) X Z).isLT = true
      · simp only [l2, ↓reduceIte]
        exact ⟨[Y, X, Z], by simp, small3 yx (islt_lt l2), swap [Z]⟩
      simp only [l2, Bool.false_eq_true, ↓reduceIte]
      by_cases e2 : Term.compare (Term.fuel X Z) X Z = .eq
      · simp only [e2, ↓reduceIte]
        exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx,
          (swap []).trans (drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := X) (by simp) e2)⟩
      simp only [e2, ↓reduceIte]
      have zx := gt_of_ne (not_islt' l2) e2
      by_cases l3 : (Term.compare (Term.fuel Z Y) Z Y).isLT = true
      · simp only [l3, ↓reduceIte]
        have s := small3 (κ := (fun x : Term => x)) (islt_lt l3) yx
        exact ⟨[Z, Y, X], by simp, s, eqv_perm (List.reverse_perm [X, Y, Z]) s.ne⟩
      simp only [l3, Bool.false_eq_true, ↓reduceIte]
      by_cases e3 : Term.compare (Term.fuel Z Y) Z Y = .eq
      · simp only [e3, ↓reduceIte]
        exact ⟨[Y, X], by simp, small2 (κ := (fun x : Term => x)) yx,
          (swap []).trans (drop_at (κ := (fun x : Term => x)) (P := [X, Y]) (L := []) (y := Y) (by simp) (c_eq_symm e3))⟩
      simp only [e3, ↓reduceIte]
      have s := small3 (κ := (fun x : Term => x)) (gt_of_ne (not_islt' l3) e3) zx
      exact ⟨[Y, Z, X], by simp, s, eqv_perm (List.perm_append_singleton X [Y, Z]) s.ne⟩
    | Z :: W :: T' =>
      simp only []
      obtain ⟨R, run, s, er⟩ := (us2 (T'.length + 2)).1 X Y (Z :: W :: T') [] [] (by simp)
        (by simp [SA]; exact yx)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl; exact ky; exact kx)
        (by simp [RunsA]) kt
      exact ⟨R, by simpa using run, s, er.trans (by simpa using swap (Z :: W :: T'))⟩
  simp only [g, Bool.false_eq_true, ↓reduceIte]
  have e : Term.compare (Term.fuel X Y) X Y = .eq := by
    cases h : Term.compare (Term.fuel X Y) X Y <;> simp_all
  obtain ⟨R, run, s, er⟩ := usort1 T.length X T (by omega) kx kt
  exact ⟨R, run, s, er.trans (drop_at (κ := (fun x : Term => x)) (P := [X]) (y := X) (by simp) e)⟩

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple/1` of static elements is the closed literal of them. -/
theorem tuple_run (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«tuple/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "closed", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "closed" (Or.inr rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  cases l <;> simp_all [Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2», Term.list]

section
variable {t : Term} {n : Nat}

/-- Closed tuples of two element types: the tuples of a value of each. -/
theorem pair_sem {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b) :
    ∃ P, Elixir.Module.Types.Descr.«tuple/1» (Term.list [a, b]) = .ok P ∧ DE (level t n).E P ∧
      ∀ w, (∃ X, P = .map X ∧ TT t n X w) ↔ ∃ x y, w = [x, y] ∧ (level t n).den a x ∧ (level t n).den b y := by
  obtain ⟨k, run, key⟩ := tuple_run [a, b] (by simp [hsa, hsb])
  have hl : ∀ e ∈ [a, b], (level t n).E e := by simp [ha, hb]
  refine ⟨_, run, fused_de (Or.inr rfl) hl key, fun w => ?_⟩
  simp only [Term.map.injEq, exists_eq_left', TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true,
    Option.map_some, Option.some.injEq, denTF_leaf (level t n).ef (Or.inr rfl) hl, vT_lit (level t n).ef (Or.inr rfl) hl, equalExact_eq_decide]
  match w with
  | [] => simp [InT]
  | [x] => simp [InT]
  | [x, y] => simp only [InT, and_true, List.cons.injEq]; exact ⟨fun h => ⟨x, y, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨e₁, e₂⟩, h⟩ => e₁ ▸ e₂ ▸ h⟩
  | x :: y :: z :: r => simp [InT]

end

/-- The empty list type. -/
def nilT : Term := .map [(.atom "bitmap", .integer 4)]

theorem leaf_map_new {tag : Term} (ht : tag ≠ .atom "closed") (Y : List (Term × Term)) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (.map Y) = .ok (.tuple #[.integer k, tag, .map Y]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons tag (.map Y))
  refine ⟨hash, ?_⟩
  unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
  split
  · exact absurd rfl ht
  · simp [hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»]

/-- `list/1` and `non_empty_list/1` of a static element type: the literal of lists of its values ending in the empty
list, with the empty list for `list/1`. -/
theorem list_run {e : Term} (he : Static e) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«list/1» (D m) e =
      .ok (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, e, nilT])]) ∧
    Elixir.Module.Types.Descr.«non_empty_list/1» (D m) e = .ok (.map [(.atom "list", .tuple #[.integer k, e, nilT])]) := by
  have ne : e ≠ .atom "closed" := by rcases he with rfl | ⟨X, rfl, -⟩ | ⟨r, -, -, rfl⟩ <;> simp
  obtain ⟨k, leaf⟩ := leaf_map_new ne [(.atom "bitmap", .integer 4)]
  have sn : Static (.map [(.atom "bitmap", .integer 4)]) := Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩)
  refine ⟨k, ?_, ?_⟩
  · simp [Elixir.Module.Types.Descr.«list/1», Elixir.Module.Types.Descr.«list_descr/3», split_static he,
      split_static sn, Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.maps.«take/2», mapLookup,
      Elixir.Module.Types.Descr.«list_new/2», nilT, leaf, Lynx.Except.orElse, Erlang.erlang.«==/2»]
    by_cases h : Term.compare (Term.fuel e (.map [])) e (.map []) = .eq <;> simp [h]
  · simp [Elixir.Module.Types.Descr.«non_empty_list/1», Elixir.Module.Types.Descr.«non_empty_list/2»,
      Elixir.Module.Types.Descr.«list_descr/3», split_static he,
      split_static sn, Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.maps.«take/2», mapLookup,
      Elixir.Module.Types.Descr.«list_new/2», nilT, leaf, Lynx.Except.orElse, Erlang.erlang.«==/2»]
    by_cases h : Term.compare (Term.fuel e (.map [])) e (.map []) = .eq <;> simp [h]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The values of the elements of tuple types, as `tuple_values/1` computes them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The values a literal without negations holds at its positions: none when an element is empty, any for open
literals, and those of its elements for closed ones. -/
def PieceVal (den : Term → V → Prop) (p : Term) (y : V) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (∀ e ∈ l, ∃ y', den e y') ∧
    (tag = "open" ∨ ∃ e ∈ l, den e y)

theorem inT_get_closed : ∀ {l : List Term} {v : List V}, InT den Bool.true l v → ∀ (j : Nat) (y : V), v[j]? = some y → ∃ e ∈ l, den e y
  | [], [], _, j, y, hy => by simp at hy
  | [], _ :: _, h, _, _, _ => by simp [InT] at h
  | _ :: _, [], h, _, _, _ => by simp [InT] at h
  | x :: l, z :: v, h, j, y, hy => by
    simp only [InT] at h
    cases j with
    | zero => simp at hy; subst hy; exact ⟨x, List.mem_cons_self, h.1⟩
    | succ j =>
      obtain ⟨e, me, he⟩ := inT_get_closed h.2 j y (by simpa using hy)
      exact ⟨e, List.mem_cons_of_mem _ me, he⟩

/-- The elements of the tuples of a literal without negations are values of its positions. -/
theorem pieceIn_val {p : Term} (tp : Piece E p) {w : List V} (h : PieceIn den p w) {j : Nat} {y : V}
    (hy : w[j]? = some y) : PieceVal den p y := by
  obtain ⟨tag, l, rfl, g, -⟩ := tp
  have h := pieceIn_iff.mp h
  refine ⟨tag, l, rfl, inT_nonempty h, ?_⟩
  rcases g with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (inT_get_closed h j y hy)

theorem inT_exists_closed : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∃ w : List V, InT den Bool.true l w
  | [], _ => ⟨[], by simp [InT]⟩
  | x :: l, ne => by
    obtain ⟨yx, hx⟩ := ne x List.mem_cons_self
    obtain ⟨w, hw⟩ := inT_exists_closed (fun e me => ne e (List.mem_cons_of_mem _ me))
    exact ⟨yx :: w, by simp [InT, hx, hw]⟩

/-- Closed literals with values in every element hold a tuple with a value of any element. -/
theorem inT_witness_closed : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∀ {e : Term} {y : V}, e ∈ l → den e y →
    ∃ w, InT den Bool.true l w ∧ ∃ j : Nat, w[j]? = some y
  | [], _, _, _, me, _ => by simp at me
  | x :: l, ne, e, y, me, hy => by
    obtain ⟨y₀, hy₀⟩ := ne x List.mem_cons_self
    have ne' : ∀ e ∈ l, ∃ y', den e y' := fun e me => ne e (List.mem_cons_of_mem _ me)
    rcases List.mem_cons.mp me with rfl | me
    · obtain ⟨w, hw⟩ := inT_exists_closed ne'
      exact ⟨y :: w, by simp [InT, hy, hw], 0, by simp⟩
    · obtain ⟨w, hw, j, hj⟩ := inT_witness_closed ne' me hy
      exact ⟨y₀ :: w, by simp [InT, hy₀, hw], j + 1, by simpa using hj⟩

/-- Open literals with values in every element hold tuples of any length from theirs. -/
theorem inT_witness_open (y₀ : V) : ∀ {l : List Term}, (∀ e ∈ l, ∃ y', den e y') → ∀ N,
    ∃ w, InT den Bool.false l w ∧ N ≤ List.length w
  | [], _, N => ⟨List.replicate N y₀, InT.open_nil _, by simp⟩
  | x :: l, ne, N => by
    obtain ⟨yx, hx⟩ := ne x List.mem_cons_self
    obtain ⟨w, hw, lw⟩ := inT_witness_open y₀ (fun e me => ne e (List.mem_cons_of_mem _ me)) N
    exact ⟨yx :: w, by simp [InT, hx, hw], by simp; omega⟩

theorem inT_replicate {e : Term} : ∀ (s : Nat) (w : List V),
    InT den Bool.true (List.replicate s e) w ↔ w.length = s ∧ ∀ y ∈ w, den e y
  | 0, [] => by simp [InT]
  | 0, _ :: _ => by simp [InT]
  | _ + 1, [] => by simp [List.replicate_succ, InT]
  | s + 1, y :: w => by
    simp only [List.replicate_succ, InT, inT_replicate s w, List.length_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h, rfl, h'⟩; exact ⟨rfl, h, h'⟩
    · rintro ⟨e, h, h'⟩; exact ⟨h, by omega, h'⟩

/-- The fold of `opt_union/2` over element types unites their values. -/
theorem union_elements (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∃ r, E r ∧ Erlang.lists.«foldl/3» (D (n + 1)) (.function false "Elixir.Module.Types.Descr" "opt_union" 2 #[])
      (.map []) (Term.list l) = .ok r ∧ ∀ y, den r y ↔ ∃ e ∈ l, den e y := by
  obtain ⟨r, ⟨hr, sr⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "opt_union" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ e ∈ pre, den e y) l
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] (hl x mx) ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨e, me, h⟩)
          · exact ⟨x, Or.inr rfl, h⟩
          · exact ⟨e, Or.inl me, h⟩
        · rintro ⟨e, me | rfl, h⟩
          · exact Or.inr ⟨e, me, h⟩
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:opt_union/2».pure]
        simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨r, hr, run, sr⟩

/-- The fold of `process_tuples_values/1` over literals without negations unites the values of their positions. -/
theorem values_pieces (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (P : List Term) (tP : ∀ p ∈ P, Piece E p) :
    ∃ r, E r ∧ Erlang.lists.«foldl/3» (D (n + 2))
      (.function false "Elixir.Module.Types.Descr" "-process_tuples_values/1-fun-0-" 2 #[]) (.map []) (Term.list P) = .ok r ∧
      ∀ y, den r y ↔ ∃ p ∈ P, PieceVal den p y := by
  obtain ⟨r, ⟨hr, sr⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr" "-process_tuples_values/1-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, PieceVal den p y) P
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨tag, l, rfl, g, hl⟩ := tP x mx
      -- The value of the literal.
      have empties : ∀ e ∈ l, (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) #[e] =
          .ok (boolAtom (bp (∀ v, ¬den e v))) := by
        intro e me
        obtain ⟨b, rb, sb⟩ := ef.empty_pub (hl e me)
        rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure, rb n hn]
        congr 2
        cases b <;> cases h : bp (∀ v, ¬den e v) <;> simp_all
      have hany := any_list (D (n + 1)) _ _ _ (fun e => bp (∀ v, ¬den e v)) l empties
      obtain ⟨val, hval, rval, sval⟩ : ∃ val, E val ∧
          Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2» (D (n + 1)) (.tuple #[.atom tag, Term.list l]) a =
            Elixir.Module.Types.Descr.«opt_union/2» (D (n + 1)) val a ∧
          ∀ y, den val y ↔ PieceVal den (.tuple #[.atom tag, Term.list l]) y := by
        by_cases emp : ∃ e ∈ l, ∀ v, ¬den e v
        · have t : (l.any fun e => bp (∀ v, ¬den e v)) = Bool.true := by
            obtain ⟨e, me, he⟩ := emp
            exact List.any_eq_true.mpr ⟨e, me, bp_true.mpr he⟩
          refine ⟨.map [], ef.none, ?_, fun y => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, t, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure]
          · simp only [ef.den_none y, false_iff]
            rintro ⟨tag', l', e, ne, -⟩
            simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
            obtain ⟨rfl, e⟩ := e
            obtain rfl := list_inj e
            obtain ⟨e', me', he'⟩ := emp
            obtain ⟨y', hy'⟩ := ne e' me'
            exact he' y' hy'
        · have f : (l.any fun e => bp (∀ v, ¬den e v)) = Bool.false := by
            cases h : l.any fun e => bp (∀ v, ¬den e v)
            · rfl
            · obtain ⟨e, me, he⟩ := List.any_eq_true.mp h
              exact absurd ⟨e, me, bp_true.mp he⟩ emp
          have ne : ∀ e ∈ l, ∃ y', den e y' := fun e me =>
            Classical.byContradiction fun h => emp ⟨e, me, fun v hv => h ⟨v, hv⟩⟩
          have pv : ∀ y, PieceVal den (.tuple #[.atom tag, Term.list l]) y ↔ tag = "open" ∨ ∃ e ∈ l, den e y := by
            intro y
            constructor
            · rintro ⟨tag', l', e, -, h⟩
              simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
              obtain ⟨rfl, e⟩ := e
              obtain rfl := list_inj e
              exact h
            · intro h; exact ⟨tag, l, rfl, ne, h⟩
          rcases g with rfl | rfl
          · refine ⟨.atom "term", ef.term, ?_, fun y => by rw [pv]; simp [ef.den_term y]⟩
            simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, f, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», Erlang.erlang.«==/2», pure, Except.pure]
          · obtain ⟨u, hu, ru, su⟩ := union_elements ef hn l hl
            refine ⟨u, hu, ?_, fun y => by rw [pv, su]; simp⟩
            simp [Elixir.Module.Types.Descr.«-process_tuples_values/1-fun-0-/2», hany, f, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«/=/2», Erlang.erlang.«==/2», pure, Except.pure, ru]
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hval ha (show K ≤ n + 1 by omega)
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa, sval]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, Or.inr rfl, h⟩
          · exact ⟨p, Or.inl mp, h⟩
        · rintro ⟨p, mp | rfl, h⟩
          · exact Or.inr ⟨p, mp, h⟩
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-process_tuples_values/1-fun-0-/2».pure, rval]
        simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨r, hr, run, sr⟩

end

section
variable {t : Term} {n : Nat}

theorem dnf_top (k : Int) (m : Nat) : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (m + 10))
    (.tuple #[.integer k, .atom "open", .nil]) = .ok (Term.list [.tuple #[.atom "open", .nil]]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1»]
  rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]
  simp [Elixir.Module.Types.Descr.«tuple_line_intersection/2», Erlang.erlang.«length/1»,
    Elixir.Module.Types.Descr.«tuple_sizes_strategy/4», Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«flatmap/2», Erlang.lists.«flatmap_1/2»,
    Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», Elixir.Module.Types.Descr.«tuple_eliminate_negations/3»,
    Elixir.Module.Types.Descr.«dedup_contiguous/1», Erlang.lists.«reverse/2», Erlang.erlang.«is_function/2»,
    Erlang.lists.«any/2», Erlang.lists.«foldl/3»]

/-- `tuple_values/1` on static types of the next level: `:badtuple` on types not only of tuples, and otherwise the values
of the positions of literals without negations holding the tuples of the type. -/
theorem values_cases {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨
        (TOnly t n X ∧ (level t n).E res ∧ ∃ P : List Term, (∀ p ∈ P, Piece (level t n).E p) ∧
          (∀ w, (∃ p ∈ P, PieceIn (level t n).den p w) ↔ TT t n X w) ∧
          ∀ y, (level t n).den res y ↔ ∃ p ∈ P, PieceVal (level t n).den p y)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    have nonly : ¬TOnly t n X := fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h
    refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, nonly⟩⟩
    rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
    by_cases e : X = []
    · subst e; simp [Erlang.erlang.«==/2», pure, Except.pure]
    · have ne : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2»]; intro h; exact e (by cases X <;> simp_all)
      simp [ne, Erlang.maps.«take/2», sX.static, hb,
        Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Lynx.Term.isMember, pure, Except.pure]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    have ne : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
      have : X ≠ [] := by intro h; subst h; simp [mapLookup] at hb
      simp [Erlang.erlang.«==/2»]; intro h; exact this (by cases X <;> simp_all)
    obtain ⟨c, rc, sc⟩ := only_run hX hb (m := k + 4) (by omega)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have get : Elixir.Map.«get/3» (.map X) (.atom "tuple") (.atom "bdd_bot") = .ok b := by
      simp [Elixir.Map.«get/3», getMapKeys_single, hb, pure, Except.pure]
    by_cases ok : TOnly t n X
    · have c_true : c = Bool.true := sc.mpr ok
      subst c_true
      -- The literals of the tuple field.
      obtain ⟨P, rP, tP, sP⟩ : ∃ P : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (k + 4)) b =
          .ok (Term.list P) ∧ (∀ p ∈ P, Piece (level t n).E p) ∧
          ∀ w, (∃ p ∈ P, PieceIn (level t n).den p w) ↔ TT t n X w := by
        rcases fb with ⟨k', rfl⟩ | wb
        · have e : k - 6 + 10 = k + 4 := by rw [level_K] at hm; omega
          refine ⟨_, by simpa [e] using dnf_top k' (k - 6), fun p mp => ?_, fun w => ?_⟩
          · simp at mp; subst mp; exact ⟨"open", [], rfl, Or.inl rfl, by simp⟩
          · rw [tt, denTF_top]
            simp only [List.mem_singleton, exists_eq_left, iff_true]
            exact ⟨"open", [], rfl, InT.open_nil w⟩
        · obtain ⟨P, rP, tP, sP⟩ := no_negs (den := (level t n).den) ef (n := k + 1) (by rw [level_K] at hm ⊢; omega) wb
          exact ⟨P, rP, tP, fun w => by rw [sP, tt, denTF_bdd wb]⟩
      obtain ⟨r, hr, rr, sr⟩ := values_pieces ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) P tP
      refine ⟨r, ?_, Or.inr ⟨ok, hr, P, tP, sP, sr⟩⟩
      rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
      simp [ne, Erlang.maps.«take/2», sX.static, rc, boolAtom, Lynx.Term.isMember, get,
        Elixir.Module.Types.Descr.«process_tuples_values/1», rP, rr, pure, Except.pure]
    · have c_false : c = Bool.false := by
        cases c
        · rfl
        · exact absurd (sc.mp rfl) ok
      subst c_false
      refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, ok⟩⟩
      rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
      simp [ne, Erlang.maps.«take/2», sX.static, rc, boolAtom, Lynx.Term.isMember, pure, Except.pure]

/-- `sizes?/1` holds of lists of natural numbers. -/
theorem sizes_nat : ∀ {s : Term}, «sizes?/1» s = .ok (.atom "true") → ∃ ns : List Nat, s = Term.list (ns.map fun k : Nat => Term.integer (k : Int))
  | .cons a rest, h => by
    simp only [«sizes?/1», Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hn⟩, hr⟩ := h
    obtain ⟨z, rfl⟩ : ∃ z : Int, a = .integer z := by
      cases a <;> simp [Erlang.erlang.«is_integer/1»] at ha
      exact ⟨_, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k : Nat, z = k := by
      refine ⟨z.toNat, ?_⟩
      by_cases neg : z < 0
      · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hn
      · omega
    obtain ⟨ns, rfl⟩ := sizes_nat hr
    exact ⟨k :: ns, rfl⟩
  | .nil, _ => ⟨[], rfl⟩
  | .atom _, h | .integer _, h | .float _, h | .tuple _, h | .map _, h | .bitstring _ _ _, h
  | .function _ _ _ _ _, h | .pid _, h | .reference _, h => by
    simp [«sizes?/1», Erlang.erlang.«==/2»] at h

/-- `closed_tuples/2` gives closed tuples of the sizes, of values of the type. -/
theorem closed_tuples_sem {v : Term} (hv : (level t n).E v) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∀ ns : List Nat, ∃ C, «closed_tuples/2» (D m) (Term.list (ns.map fun k : Nat => Term.integer (k : Int))) v = .ok C ∧
      DE (level t n).E C ∧ ∀ w, denD C (tpt (t := t) (n := n) w) → List.length w ∈ ns ∧ ∀ y ∈ w, (level t n).den v y
  | [] => ⟨.map [], by simp [«closed_tuples/2», Elixir.Module.Types.Descr.«none/0»],
      Or.inr ⟨[], rfl, descrC_nil⟩, fun w h => by rw [denD_map] at h; simp [mapLookup, tpt, dn_none] at h⟩
  | s :: ns => by
    obtain ⟨C', rC, dC, sC⟩ := closed_tuples_sem hv hm ns
    have hl : ∀ e ∈ List.replicate s v, (level t n).E e := fun e me => by rw [List.eq_of_mem_replicate me]; exact hv
    obtain ⟨k, rt, key⟩ := tuple_run (List.replicate s v) fun e me => (level t n).ef.static (hl e me)
    have dT := fused_de (Or.inr rfl) hl key
    obtain ⟨c, tc, rc, sc⟩ := tc_union (L := level t n) dT dC (m := m) (by omega)
    refine ⟨c, ?_, tc, fun w h => ?_⟩
    · simp [«closed_tuples/2», dup_nat, rt, rC, rc]
    · rcases (sc _).mp h with h | h
      · rw [denD_tpt] at h
        simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
          Option.some.injEq, exists_eq_left', denTF_leaf (level t n).ef (Or.inr rfl) hl,
          vT_lit (level t n).ef (Or.inr rfl) hl, equalExact_eq_decide] at h
        obtain ⟨len, hy⟩ := (inT_replicate s w).mp (by simpa using h)
        exact ⟨by simp [len], hy⟩
      · obtain ⟨len, hy⟩ := sC w h
        exact ⟨List.mem_cons_of_mem _ len, hy⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Values of the level above, as points. -/
def toPN (y : (level t (n + 1)).V) : PN t n := y

theorem den_succ {a : Term} (ha : DE (level t n).E a) (v : PN t n) : (level t (n + 1)).den a v ↔ denD a v :=
  denN_of (DEG.notT ha)

theorem e_succ {a : Term} (ha : DE (level t n).E a) : (level t (n + 1)).E a := Or.inl ha

theorem nilT_de : DE (level t n).E nilT :=
  single_de (by simp [names]) (Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩)

theorem nilT_den (v : PN t n) : denD nilT v ↔ v.1.1 = "bitmap" ∧ v.1.2.1 = 2 := by
  rw [nilT, denD_single]
  simp only [dn_bitmap, bitOf, and_congr_right_iff]
  intro _
  have : (4 : Int).toNat = 2 ^ 2 := rfl
  rw [this, Nat.testBit_two_pow]
  simp [eq_comm]

/-- The empty list point. -/
def nilPt : PN t n := bPt 2 (by omega)

theorem nilPt_den : denD nilT (nilPt (t := t) (n := n)) := (nilT_den _).mpr ⟨rfl, rfl⟩

/-- List literals of element types of lists ending in the empty list. -/
theorem lf_nil {inner : Term} (hi : DE (level t n).E inner) (k : Int) :
    LF (level t (n + 1)).E (.tuple #[.integer k, inner, nilT]) :=
  Bdd.leaf_iff.mpr ⟨k, inner, nilT, rfl, e_succ hi, e_succ nilT_de⟩

/-- The point of a non-empty list of values of the next level. -/
noncomputable def lpt (v : LV (level t (n + 1)).V) (h : ListVal (level t (n + 1)).tl v) : PN t (n + 1) :=
  ⟨("list", (0, .nil, valL (level t (n + 1)).E (level t (n + 1)).den v)), by simp [names],
    ⟨valL_resp v, fun h => by simp at h, fun _ => ⟨v, h, rfl⟩, fun h => by simp at h, fun h => by simp at h,
      fun h => by simp at h⟩⟩

theorem list_val (q : PN t (n + 1)) (h : q.1.1 = "list") :
    ∃ v : LV (level t (n + 1)).V, ListVal (level t (n + 1)).tl v ∧
      q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := q
  simp only at h
  subst h
  obtain ⟨v, hv, e⟩ := ok.2.2.1 rfl
  exact ⟨v, hv, e⟩

/-- Lists of the literal of lists of an element type ending in the empty list. -/
theorem dn_nil_list {inner : Term} (hi : DE (level t n).E inner) (k : Int) {p : Point} {v : LV (level t (n + 1)).V}
    (e : p.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v) :
    dn "list" (some (.tuple #[.integer k, inner, nilT])) p = Bool.true ↔
      (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last) := by
  rw [dn_listL (level t (n + 1)).ef (lf_nil hi k) e, dL, eval_leaf,
    valL_iff (level t (n + 1)).ef.semR ⟨k, inner, nilT, rfl, e_succ hi, e_succ nilT_de⟩, llitSem_iff]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun y m => (den_succ hi (toPN y)).mp (h₁ y m), (den_succ nilT_de (toPN v.last)).mp h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun y m => (den_succ hi (toPN y)).mpr (h₁ y m), (den_succ nilT_de (toPN v.last)).mpr h₂⟩⟩

/-- The list types of element types: lists of them ending in the empty list, and the empty list when `nil` holds. -/
def lTy (nil : Bool) (k : Int) (inner : Term) : Term :=
  if nil then .map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
  else .map [(.atom "list", .tuple #[.integer k, inner, nilT])]

theorem lTy_de (nil : Bool) (k : Int) {inner : Term} (hi : DE (level t n).E inner) :
    DE (level t (n + 1)).E (lTy nil k inner) := by
  have fl : FieldC (FunA (level t (n + 1)).E) (TField (level t (n + 1)).E) (LF (level t (n + 1)).E)
      (MField (level t (n + 1)).E) "list" (.tuple #[.integer k, inner, nilT]) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_nil hi k⟩)))
  cases nil
  · exact single_de (by simp [names]) fl
  · refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
    · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
      by_cases e : compareExact (fuel q (.atom "bitmap")) q (.atom "bitmap") = .eq
      · exact ⟨"bitmap", by simp [names], (compareExact_eq_atom _ _).mp e⟩
      · by_cases e' : compareExact (fuel q (.atom "list")) q (.atom "list") = .eq
        · exact ⟨"list", by simp [names], (compareExact_eq_atom _ _).mp e'⟩
        · simp [e, e'] at h
    · rw [lookup_cons_atom, lookup_cons_atom] at h
      by_cases e : "bitmap" = name
      · subst e; simp at h; subst h; exact Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩
      · by_cases e' : "list" = name
        · subst e'; simp at h; subst h; exact fl
        · simp [e, e', mapLookup] at h

/-- The points of list types: the empty list when it holds it, and the lists of its element type ending in the empty
list. -/
theorem lTy_den (nil : Bool) (k : Int) {inner : Term} (hi : DE (level t n).E inner) (q : PN t (n + 1)) :
    denD (lTy nil k inner) q ↔ (nil = Bool.true ∧ q.1.1 = "bitmap" ∧ q.1.2.1 = 2) ∨
      (q.1.1 = "list" ∧ ∀ v : LV (level t (n + 1)).V, q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v →
        (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last)) := by
  by_cases hl : q.1.1 = "list"
  · obtain ⟨v, -, hv⟩ := list_val q hl
    have hdn := fun (v' : LV (level t (n + 1)).V) (e : q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v') =>
      dn_nil_list (p := q.1.2) hi k e
    have key : dn "list" (some (.tuple #[.integer k, inner, nilT])) q.1.2 = Bool.true ↔
        ∀ v : LV (level t (n + 1)).V, q.1.2.2.2 = valL (level t (n + 1)).E (level t (n + 1)).den v →
          (∀ y ∈ v.xs, denD inner (toPN y)) ∧ denD nilT (toPN v.last) :=
      ⟨fun h v' e => (hdn v' e).mp h, fun h => (hdn v hv).mpr (h v hv)⟩
    cases nil <;> simp [lTy, denD_map, hl, mapLookup] <;> exact key
  · cases nil
    · simp [lTy, denD_map, hl, mapLookup, dn_none]
    · by_cases hb : q.1.1 = "bitmap"
      · have look : mapLookup [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
            (.atom "bitmap") = some (.integer 4) := by simp [mapLookup]
        simp only [lTy, ite_true, denD_map, hb, look, true_and]
        rw [dn_bitmap, bitOf]
        have : (4 : Int).toNat = 2 ^ 2 := rfl
        rw [this, Nat.testBit_two_pow]
        simp [eq_comm]
      · have look : mapLookup [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer k, inner, nilT])]
            (.atom q.1.1) = none := by
          rw [lookup_cons_atom, lookup_cons_atom]; simp [Ne.symm hb, Ne.symm hl, mapLookup]
        simp [lTy, denD_map, look, dn_none, hb, hl]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem foldl1_err {m : Nat} (f : Term) (R : List Term → Term → Prop) (Q : Term → Prop) (e : Exception)
    (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → (∃ a', R (pre ++ [x]) a' ∧ (D m).pure f #[x, a] = .ok a') ∨
      (Q x ∧ (D m).pure f #[x, a] = .error e)) :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      (∃ r, R (pre ++ rest) r ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r) ∨
        (∃ x ∈ rest, Q x ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .error e) := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact Or.inl ⟨acc, by simpa using h, by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    rcases step pre x acc (sub x List.mem_cons_self) h with ⟨a', h', run⟩ | ⟨q, run⟩
    · rcases ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h' with ⟨r, hr, rest⟩ | ⟨y, my, q, rest⟩
      · refine Or.inl ⟨r, by simpa using hr, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at rest ⊢
        simp only [run, Lynx.Except.ok_bind]
        exact rest
      · refine Or.inr ⟨y, List.mem_cons_of_mem _ my, q, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at rest ⊢
        simp only [run, Lynx.Except.ok_bind]
        exact rest
    · refine Or.inr ⟨x, List.mem_cons_self, q, ?_⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [run]
      rfl

/-- Folds whose steps either keep a relation or fail with an exception. -/
theorem foldl_err {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (Q : Term → Prop)
    (e : Exception) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → (∃ a', R (pre ++ [x]) a' ∧ (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok a') ∨
      (Q x ∧ (D m).pure (.function false mo nm 2 caps) #[x, a] = .error e)) (acc : Term) (h : R [] acc) :
    (∃ r, R l r ∧ Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .ok r) ∨
      (∃ x ∈ l, Q x ∧ Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .error e) := by
  have run := foldl1_err (.function false mo nm 2 caps) R Q e l step l [] acc (fun _ h => h) h
  have eq : Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) =
      Erlang.lists.«foldl_1/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) := by
    cases l with
    | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»]
    | cons x xs =>
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list]
      rw [Erlang.lists.«foldl_1/3».eq_def]
  rw [eq]
  simpa using run

section
variable {t : Term} {n : Nat}

/-- Points of pairs of a value of each of two types. -/
def PairPt (t : Term) (n : Nat) (a b : Term) (p : PN t n) : Prop :=
  ∃ w : List (level t n).V, (∀ X, denD (.map X) p ↔ TT t n X w) ∧
    ∃ x y, w = [x, y] ∧ (level t n).den a x ∧ (level t n).den b y

/-- `tuple/1` of two element types holds the pairs of their values. -/
theorem pair_run {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b) :
    ∃ P, Elixir.Module.Types.Descr.«tuple/1» (Term.list [a, b]) = .ok P ∧ DE (level t n).E P ∧
      ∀ p : PN t n, denD P p ↔ PairPt t n a b p := by
  obtain ⟨P, run, dP, sP⟩ := pair_sem ha hb hsa hsb
  obtain ⟨k, run', -⟩ := tuple_run [a, b] (by simp [hsa, hsb])
  rw [run] at run'
  cases run'
  refine ⟨_, run, dP, fun p => ?_⟩
  constructor
  · intro hp
    have ht : p.1.1 = "tuple" := by
      rw [denD_map] at hp
      by_cases h : p.1.1 = "tuple"
      · exact h
      · simp [mapLookup, h, dn_none] at hp
    obtain ⟨w, hw⟩ := pt_tuple p ht
    exact ⟨w, hw, (sP w).mp ⟨_, rfl, (hw _).mp hp⟩⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨X, e, hX⟩ := (sP w).mpr h
    cases e
    exact (hw _).mpr hX

end

section
variable {t : Term} {n : Nat}

theorem bitKind_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : bitKind i = bitKind j) : i = j := by
  match i, hi, j, hj with
  | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ | 4, _, 4, _ | 5, _, 5, _ | 6, _, 6, _ | 7, _, 7, _ => rfl
  | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
  | 1, _, 0, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
  | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
  | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 6, _ | 5, _, 7, _
  | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 7, _
  | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ => simp [bitKind] at h

/-- Types of the keys of a kind, as `domain_key_to_descr/1` gives them: all points of that kind. -/
structure DomT (t : Term) (n : Nat) (d : String) (T : Term) : Prop where
  de : DE (level t n).E T
  static : Static T
  atoms : d = "atom" → ∀ v : PN t n, v.1.1 = "atom" → denD T v
  kinds : d ≠ "atom" → ∀ v : PN t n, ptKind v = d → denD T v

theorem domT_bit (i : Nat) (hi : i < 8) (ni : i ≠ 2) :
    DomT t n (bitKind i) (.map [(.atom "bitmap", .integer ((2 ^ i : Nat) : Int))]) := by
  have kb := kind_bit (t := t) (n := n) i hi
  refine ⟨kb.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => absurd h ?_, fun _ v hv => ?_⟩
  · match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind]
  rw [denD_single]
  by_cases hb : v.1.1 = "bitmap"
  · have hp : v.1.2.1 < 8 := v.2.2.2.1 hb
    have := bitKind_inj hp hi (by simpa [ptKind, hb] using hv)
    refine ⟨hb, ?_⟩
    simp only [dn_bitmap, bitOf, Int.toNat_natCast, this, Nat.testBit_two_pow_self]
  · exfalso
    have hn := v.2.1
    simp only [ptKind, hb, ite_false] at hv
    rw [hv] at hn
    match i, hi, ni with
    | 0, _, _ | 1, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ => simp [bitKind, names] at hn

end

section
variable {t : Term} {n : Nat}

theorem bitKind_mem (i : Nat) : bitKind i ∈ ["binary", "bitstring_no_binary", "list", "integer", "float", "pid", "port",
    "reference"] := by
  unfold bitKind; split <;> simp

/-- Points of a kind outside the bitmap kinds are of that field. -/
theorem ptKind_field {v : PN t n} {d : String} (h : ptKind v = d) (hd : d = "atom" ∨ d = "fun" ∨ d = "map" ∨ d = "tuple") :
    v.1.1 = d := by
  unfold ptKind at h
  split at h
  · have := bitKind_mem v.1.2.1
    rw [h] at this
    rcases hd with rfl | rfl | rfl | rfl <;> simp at this
  · exact h

theorem domT_list : DomT t n "list"
    (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) := by
  have fl : FieldC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) "list"
      (.tuple #[.integer 46675407, .atom "term", .atom "term"]) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr ⟨_, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩)))
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩),
    fun h => by simp at h, fun _ v hv => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases e : compareExact (fuel q (.atom "bitmap")) q (.atom "bitmap") = .eq
    · exact ⟨"bitmap", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · by_cases e' : compareExact (fuel q (.atom "list")) q (.atom "list") = .eq
      · exact ⟨"list", by simp [names], (compareExact_eq_atom _ _).mp e'⟩
      · simp [e, e'] at h
  · rw [lookup_cons_atom, lookup_cons_atom] at h
    by_cases e : "bitmap" = name
    · subst e; simp at h; subst h; exact Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩
    · by_cases e' : "list" = name
      · subst e'; simp at h; subst h; exact fl
      · simp [e, e', mapLookup] at h
  · rw [denD_map]
    unfold ptKind at hv
    split at hv
    · rename_i hb
      have hp : v.1.2.1 < 8 := v.2.2.2.1 hb
      have : v.1.2.1 = 2 := bitKind_inj hp (by omega) hv
      rw [hb]
      simp [mapLookup, dn_bitmap, bitOf, this]
      decide
    · rw [hv]
      simp [mapLookup, dn_list, denL, isListTop]

/-- `domain_key_to_descr/1` gives every point of a kind. -/
theorem dkd_run {d : String} (hd : d ∈ domainKinds) :
    ∃ T, Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok T ∧ DomT t n d T := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, rfl, kind_atom.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun _ v hv => ?_,
      fun h => absurd rfl h⟩
    rw [denD_single]; exact ⟨hv, by simp [dn_atom, amemV, mapLookup]⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 0 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 1 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 4 (by omega) (by omega)⟩
  · refine ⟨_, rfl, kind_fun.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => ?_⟩
    rw [denD_single]; exact ⟨ptKind_field hv (by simp), dn_funTop _⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 3 (by omega) (by omega)⟩
  · exact ⟨_, rfl, domT_list⟩
  · refine ⟨_, rfl, mapTop_de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => (mapTop_den v).mpr (ptKind_field hv (by simp))⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 5 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 6 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 7 (by omega) (by omega)⟩
  · refine ⟨_, rfl, tupleTop_de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => (tupleTop_den v).mpr (ptKind_field hv (by simp))⟩

end

/-- The pair function `map_to_list/1` passes. -/
def mtlF : Term := .function false "Elixir.Module.Types.Descr" "-map_to_list/1-fun-0-" 2 #[]

/-- The type `domain_key_to_descr/1` gives a kind. -/
def dkdT (d : String) : Term :=
  match Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) with
  | .ok T => T
  | .error _ => .map []

section
variable {t : Term} {n : Nat}

theorem dkdT_run {d : String} (hd : d ∈ domainKinds) :
    Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok (dkdT d) ∧ DomT t n d (dkdT d) := by
  obtain ⟨T, run, hT⟩ := dkd_run (t := t) (n := n) hd
  have e : dkdT d = T := by simp [dkdT, run]
  rw [e]
  exact ⟨run, hT⟩

/-- Pairs of key and value types, as the pair function of `map_to_list/1` builds them. -/
theorem mtl_pair {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b)
    (m : Nat) : ∃ P, (D m).pure mtlF #[a, b] = .ok P ∧ DE (level t n).E P ∧
      ∀ p : PN t n, denD P p ↔ PairPt t n a b p := by
  obtain ⟨P, run, dP, sP⟩ := pair_run ha hb hsa hsb
  refine ⟨P, ?_, dP, sP⟩
  rw [mtlF, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list/1-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-map_to_list/1-fun-0-/2»] using run

/-- Pairs of the domains of a tag with values. -/
def DomPair (t : Term) (n : Nat) (dl : List (Term × Term)) (p : PN t (n + 1)) : Prop :=
  ∃ d v, (Term.atom d, v) ∈ dl ∧ d ∈ domainKinds ∧ (∃ x, (level t (n + 1)).den v x) ∧
    PairPt t (n + 1) (dkdT d) v p

/-- `orddict:fold/3` of `map_to_list_static/3` over domains unites the pairs of their kinds and non-empty types. -/
theorem dom_pairs {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) : ∀ (dl : List (Term × Term)),
    DomsV (level t (n + 1)).E dl → ∀ acc, DE (level t (n + 1)).E acc →
    ∃ acc', Erlang.orddict.«fold/3» (D (M + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-0-" 3 #[mtlF]) acc (fieldsTerm dl) = .ok acc' ∧
      DE (level t (n + 1)).E acc' ∧ ∀ p, denD acc' p ↔ denD acc p ∨ DomPair t n dl p
  | [], _, acc, ha => ⟨acc, by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], ha, fun p => by simp [DomPair]⟩
  | (k, v) :: rest, dv, acc, ha => by
    obtain ⟨⟨d, rfl, md⟩, hv⟩ := dv.1 _ List.mem_cons_self
    have dv' : DomsV (level t (n + 1)).E rest := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    obtain ⟨T, rT, hT⟩ : ∃ T, Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok T ∧ T = dkdT d :=
      ⟨_, (dkdT_run (t := t) (n := n) md).1, rfl⟩
    subst hT
    have dT := (dkdT_run (t := t) (n := n) md).2
    obtain ⟨eb, reb, seb⟩ := (level t (n + 1)).ef.empty_pub hv
    have step : ∃ a', Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4» (D M) mtlF (.atom d) v acc = .ok a' ∧
        DE (level t (n + 1)).E a' ∧ ∀ p, denD a' p ↔ denD acc p ∨
          ((∃ x, (level t (n + 1)).den v x) ∧ PairPt t (n + 1) (dkdT d) v p) := by
      cases eb
      · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (e_succ dT.de) hv dT.static
          ((level t (n + 1)).ef.static hv) M
        obtain ⟨c, hc, rc, sc⟩ := (ef_next t (n + 1)).opt_union [] ha dP (m := M) hM
        refine ⟨c, ?_, hc, fun p => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4», reb M (by rw [level_K] at hM ⊢; omega),
            Lynx.Term.isMember, boolAtom, rT, rP, Elixir.Module.Types.Descr.«opt_union/2», rc]
        · rw [sc, sP]
          have ne : ∃ x, (level t (n + 1)).den v x := Classical.byContradiction fun h =>
            absurd (seb.mpr fun x hx => h ⟨x, hx⟩) (by simp)
          simp [ne]
      · refine ⟨acc, ?_, ha, fun p => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4», reb M (by rw [level_K] at hM ⊢; omega),
            Lynx.Term.isMember, boolAtom]
        · have ne : ¬∃ x, (level t (n + 1)).den v x := fun ⟨x, hx⟩ => seb.mp rfl x hx
          simp [ne]
    obtain ⟨a', ra, da, sa⟩ := step
    obtain ⟨acc', run, dacc, sacc⟩ := dom_pairs hM rest dv' a' da
    refine ⟨acc', ?_, dacc, fun p => ?_⟩
    · rw [Erlang.orddict.«fold/3».eq_def]
      simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-0-/3».pure, ra, run]
    · rw [sacc, sa]
      simp only [DomPair, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ((h | ⟨ne, h⟩) | ⟨d', v', m', hd', ne', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨d, v, Or.inl ⟨rfl, rfl⟩, md, ne, h⟩
        · exact Or.inr ⟨d', v', Or.inr m', hd', ne', h⟩
      · rintro (h | ⟨d', v', ⟨e₁, rfl⟩ | m', hd', ne', h⟩)
        · exact Or.inl (Or.inl h)
        · cases e₁; exact Or.inl (Or.inr ⟨ne', h⟩)
        · exact Or.inr ⟨d', v', m', hd', ne', h⟩

end

section
variable {t : Term} {n : Nat}

/-- Pairs that a line of a map type contributes through its domains. -/
def LinePairs (t : Term) (n : Nat) (L : Term) (p : PN t (n + 1)) : Prop :=
  ∃ (dl l : List (Term × Term)) (negs : List Term), L = .tuple #[fieldsTerm dl, fieldsTerm l, Term.list negs] ∧
    DomPair t n dl p

/-- Lines with an open tag. -/
def OpenLine (L : Term) : Prop := ∃ (l : Term) (negs : Term), L = .tuple #[.atom "open", l, negs]

theorem line_pairs_step {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {L : Term} (hL : MLine (level t (n + 1)).E L)
    {acc : Term} (ha : DE (level t (n + 1)).E acc) :
    (OpenLine L ∧ (D (M + 2)).pure (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF])
        #[L, acc] = .error (.throw (.atom "open"))) ∨
      (¬OpenLine L ∧ ∃ a', (D (M + 2)).pure (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF])
        #[L, acc] = .ok a' ∧ DE (level t (n + 1)).E a' ∧ ∀ p, denD a' p ↔ denD acc p ∨ LinePairs t n L p) := by
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hL
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-1-/2».pure]
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · exact Or.inl ⟨⟨_, _, rfl⟩, by simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3»]⟩
  · refine Or.inr ⟨fun ⟨_, _, e⟩ => by simp at e, acc, ?_, ha, fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3», Erlang.erlang.«is_list/1»]
    · simp only [LinePairs, iff_self_or]
      rintro ⟨dl, l', negs', e, -⟩
      obtain ⟨e₁, -, -⟩ := tuple3_inj e
      exact absurd e₁ (fieldsTerm_ne_atom dl "closed").symm
  · obtain ⟨a', run, da, sa⟩ := dom_pairs (t := t) (n := n) (M := M) hM dl dv acc ha
    refine Or.inr ⟨fun ⟨_, _, e⟩ => (fieldsTerm_ne_atom dl "open") (tuple3_inj e).1, a', ?_, da, fun p => ?_⟩
    · have ne := fieldsTerm_ne_atom dl
      have il := is_list_fieldsTerm dl
      generalize hT : fieldsTerm dl = T at ne il run
      rw [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3».eq_def]
      simp only
      split
      · exact absurd rfl (ne _)
      · simp [il, run]
    · rw [sa]
      refine or_congr Iff.rfl ⟨fun h => ⟨dl, l, negs, rfl, h⟩, fun ⟨dl', l', negs', e, h⟩ => ?_⟩
      obtain ⟨e₁, -, -⟩ := tuple3_inj e
      rwa [fieldsTerm_inj e₁]

end

section
variable {t : Term} {n : Nat}

/-- The fold of `map_to_list_static/3` over lines: the pairs of their domains, or `:open` thrown for an open line. -/
theorem lines_pairs {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L) :
    (∃ L ∈ lines, OpenLine L ∧ Erlang.lists.«foldl/3» (D (M + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF]) (.map []) (Term.list lines) =
          .error (.throw (.atom "open"))) ∨
      (∃ acc, Erlang.lists.«foldl/3» (D (M + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF]) (.map []) (Term.list lines) =
          .ok acc ∧ (∀ L ∈ lines, ¬OpenLine L) ∧ DE (level t (n + 1)).E acc ∧
        ∀ p, denD acc p ↔ ∃ L ∈ lines, LinePairs t n L p) := by
  rcases foldl_err (m := M + 2) "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" #[mtlF]
    (fun pre acc => (∀ L ∈ pre, ¬OpenLine L) ∧ DE (level t (n + 1)).E acc ∧
      ∀ p, denD acc p ↔ ∃ L ∈ pre, LinePairs t n L p) OpenLine (.throw (.atom "open")) lines
    (fun pre L a mL ⟨ho, ha, sa⟩ => by
      rcases line_pairs_step (t := t) (n := n) hM (hl L mL) ha with ⟨o, run⟩ | ⟨no, a', run, da, sa'⟩
      · exact Or.inr ⟨o, run⟩
      · refine Or.inl ⟨a', ⟨fun L' mL' => ?_, da, fun p => ?_⟩, run⟩
        · rcases List.mem_append.mp mL' with h | h
          · exact ho L' h
          · simp at h; subst h; exact no
        · rw [sa', sa]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (⟨L', m', h⟩ | h)
            · exact ⟨L', Or.inl m', h⟩
            · exact ⟨L, Or.inr rfl, h⟩
          · rintro ⟨L', m' | rfl, h⟩
            · exact Or.inl ⟨L', m', h⟩
            · exact Or.inr h)
    (.map []) ⟨by simp, de_none, fun p => by simp [denD_map, mapLookup, dn_none]⟩ with
    ⟨r, ⟨ho, dr, sr⟩, run⟩ | ⟨L, mL, o, run⟩
  · exact Or.inr ⟨r, run, ho, dr, sr⟩
  · exact Or.inl ⟨L, mL, o, run⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The type of a single atom, as `atom/1` builds it. -/
def atomT (s : String) : Term := .map [(.atom "atom", .tuple #[.atom "union", .map [(.atom s, .nil)]])]

theorem atom_one (s : String) : Elixir.Module.Types.Descr.«atom/1» (Term.list [.atom s]) = .ok (atomT s) := by
  have pl : Term.properList? (Term.cons (.atom s) .nil) = some [.atom s] := Term.properList?_list [.atom s]
  simp [Elixir.Module.Types.Descr.«atom/1», Elixir.Module.Types.Descr.«atom_new/1», Erlang.erlang.«is_list/1»,
    Erlang.sets.«from_list/2», Erlang.sets.«from_list/1», atomT, Term.list, pl]

section
variable {t : Term} {n : Nat}

theorem atomT_de (s : String) : DE (level t n).E (atomT s) :=
  single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, _, rfl, by simp [Erlang.sets.elements?]⟩, .atom s,
    by simp [amemV, mapLookup]⟩))

theorem atomT_static (s : String) : Static (atomT s) := Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩)

theorem atomT_den (s : String) (v : PN t n) : denD (atomT s) v ↔ v.1.1 = "atom" ∧ v.1.2.2.1 = .atom s := by
  rw [atomT, denD_single]
  simp [dn_atom, amemV, mapLookup]

/-- Pairs of an atom key and the values at that key of the maps of lines. -/
def AtomPair (t : Term) (n : Nat) (lines : List Term) (s : String) (p : PN t (n + 1)) : Prop :=
  ∃ w : List (level t (n + 1)).V, (∀ X, denD (.map X) p ↔ TT t (n + 1) X w) ∧
    ∃ k x, w = [k, x] ∧ (level t (n + 1)).den (atomT s) k ∧ ∃ L ∈ lines, LongM (level t (n + 1)).den L s (some x)

end

section
variable {t : Term} {n : Nat}

/-- Seen keys: atoms mapped to `[]`. -/
def SeenOk (S : List (Term × Term)) : Prop := ∀ e ∈ S, ∃ s, e = (.atom s, .nil)

/-- Accumulated pairs: those of an initial type, and of the atom keys seen. -/
def AccOk (t : Term) (n : Nat) (lines : List Term) (acc₀ : Term) (S : List (Term × Term)) (acc : Term) : Prop :=
  DE (level t (n + 1)).E acc ∧ ∀ p, denD acc p ↔ denD acc₀ p ∨ ∃ s, (Term.atom s, Term.nil) ∈ S ∧ AtomPair t n lines s p

theorem seen_lookup {S : List (Term × Term)} (hS : SeenOk S) (s : String) :
    (mapLookup S (.atom s)).isSome = Bool.true ↔ (Term.atom s, Term.nil) ∈ S := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    rw [mapLookup] at hv
    simp only [equalExact_eq_decide] at hv
    cases e : S.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => rw [e] at hv; cases hv
    | some r =>
      have mr := List.mem_of_find?_eq_some e
      have := List.find?_some e
      simp only [decide_eq_true_eq] at this
      obtain ⟨s', rfl⟩ := hS r mr
      have : s = s' := by simpa using this
      subst this
      exact mr
  · intro h
    rw [mapLookup]
    simp only [equalExact_eq_decide]
    cases e : S.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => exact absurd (List.find?_eq_none.mp e _ h) (by simp)
    | some r => simp

/-- One field of `map_to_list_static/3`: a new atom key adds the pairs of its values in the maps of the lines. -/
theorem fetch_step {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) {acc₀ : Term}
    {S : List (Term × Term)} (hS : SeenOk S) {acc : Term} (ha : AccOk t n lines acc₀ S acc) (s : String) {f : Term}
    (hf : FieldValue (level t (n + 1)).E f) :
    ∃ S' acc', Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5» (D (M + 3)) (Term.list lines) mtlF (.atom s) f
        (.tuple #[.map S, acc]) = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (Term.atom s, Term.nil) ∈ S' ∧
      (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' := by
  obtain ⟨ty, o, rfl, -⟩ := hf
  by_cases seen : (mapLookup S (.atom s)).isSome = Bool.true
  · refine ⟨S, acc, ?_, hS, (seen_lookup hS s).mp seen, fun e me => me, ha⟩
    simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
      Lynx.Term.isMember, Term.true]
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch (level t (n + 1)).ef (n := M) (by rw [level_K] at hM ⊢; omega) s lines hl
  obtain ⟨vt, hvt, ⟨o', rfl⟩, svt⟩ := fieldValue_den (den := (level t (n + 1)).den) hF
  have vals : ∀ x, (level t (n + 1)).den vt x ↔ ∃ L ∈ lines, LongM (level t (n + 1)).den L s (some x) :=
    fun x => (svt x).trans (sF _)
  have hS' : SeenOk ((.atom s, .nil) :: S) := fun e me => (List.mem_cons.mp me).elim (fun h => ⟨s, h⟩) (hS e)
  obtain ⟨eb, reb, seb⟩ := (level t (n + 1)).ef.empty_pub hvt
  cases eb
  · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (e_succ (atomT_de s)) hvt (atomT_static s)
      ((level t (n + 1)).ef.static hvt) (M + 3)
    obtain ⟨c, hc, rc, sc⟩ := (ef_next t (n + 1)).opt_union [] ha.1 dP (m := M + 3) (by omega)
    refine ⟨(.atom s, .nil) :: S, c, ?_, hS', List.mem_cons_self, fun e me => List.mem_cons_of_mem _ me, hc, fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
        Lynx.Term.isMember, Term.false, rF, Erlang.maps.«put/3», reb (M + 3) (by rw [level_K] at hM ⊢; omega), boolAtom,
        Elixir.Module.Types.Descr.«opt_union/2»]
      rw [atom_one]
      simp [rP, rc]
    · have pe : PairPt t (n + 1) (atomT s) vt p ↔ AtomPair t n lines s p := by
        simp only [PairPt, AtomPair, vals]
      rw [sc, ha.2, sP, pe]
      simp only [List.mem_cons, Prod.mk.injEq, Term.atom.injEq, and_true]
      constructor
      · rintro ((h | ⟨s', m', h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨s', Or.inr m', h⟩
        · exact Or.inr ⟨s, Or.inl rfl, h⟩
      · rintro (h | ⟨s', e | m', h⟩)
        · exact Or.inl (Or.inl h)
        · subst e; exact Or.inr h
        · exact Or.inl (Or.inr ⟨s', m', h⟩)
  · refine ⟨(.atom s, .nil) :: S, acc, ?_, hS', List.mem_cons_self, fun e me => List.mem_cons_of_mem _ me, ha.1,
      fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-2-/5», Erlang.erlang.«is_map_key/2», any_key, seen,
        Lynx.Term.isMember, Term.false, rF, Erlang.maps.«put/3», reb (M + 3) (by rw [level_K] at hM ⊢; omega), boolAtom]
    · rw [ha.2]
      have none : ¬AtomPair t n lines s p := fun ⟨_, _, _, x, _, _, h⟩ => seb.mp rfl x ((vals x).mpr h)
      simp only [List.mem_cons, Prod.mk.injEq, Term.atom.injEq, and_true]
      constructor
      · rintro (h | ⟨s', m', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s', Or.inr m', h⟩
      · rintro (h | ⟨s', e | m', h⟩)
        · exact Or.inl h
        · subst e; exact absurd h none
        · exact Or.inr ⟨s', m', h⟩

end

section
variable {t : Term} {n : Nat}

/-- `orddict:fold/3` of `map_to_list_static/3` over the fields of a literal. -/
theorem fetch_fold {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term) :
    ∀ (l : List (Term × Term)), FieldsV (level t (n + 1)).E l → ∀ (S : List (Term × Term)) (acc : Term), SeenOk S →
      AccOk t n lines acc₀ S acc → ∃ S' acc', Erlang.orddict.«fold/3» (D (M + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-2-" 3 #[Term.list lines, mtlF])
        (.tuple #[.map S, acc]) (fieldsTerm l) = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧
        (∀ s ∈ keyStrs l, (Term.atom s, Term.nil) ∈ S') ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc'
  | [], _, S, acc, hS, ha => ⟨S, acc, by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], hS, by simp [keyStrs], fun e me => me, ha⟩
  | (k, f) :: rest, sl, S, acc, hS, ha => by
    obtain ⟨⟨s, rfl⟩, hf⟩ := sl.1 _ List.mem_cons_self
    obtain ⟨S₁, a₁, r₁, hS₁, m₁, sub₁, ha₁⟩ := fetch_step hM lines hl hS ha s hf
    obtain ⟨S₂, a₂, r₂, hS₂, m₂, sub₂, ha₂⟩ := fetch_fold hM lines hl acc₀ rest (fieldsV_tail sl) S₁ a₁ hS₁ ha₁
    refine ⟨S₂, a₂, ?_, hS₂, fun s' ms' => ?_, fun e me => sub₂ e (sub₁ e me), ha₂⟩
    · rw [Erlang.orddict.«fold/3».eq_def]
      simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-2-/3».pure, r₁, r₂]
    · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms'
      rcases ms' with rfl | ms'
      · exact sub₂ _ m₁
      · exact m₂ s' ms'

/-- Literals whose field keys are all seen. -/
def SeenNamed (S : List (Term × Term)) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    ∀ s ∈ keyStrs l, (Term.atom s, Term.nil) ∈ S

theorem seenNamed_mono {a b : List (Term × Term)} (h : ∀ e ∈ a, e ∈ b) {t : Term} (ht : SeenNamed a t) :
    SeenNamed b t :=
  fun k tag l e s ms => h _ (ht k tag l e s ms)

theorem fetch_leaf {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term)
    {lit : Term} (hlit : MapLitV (level t (n + 1)).E lit) (S : List (Term × Term)) (acc : Term) (hS : SeenOk S)
    (ha : AccOk t n lines acc₀ S acc) :
    ∃ S' acc', Lynx.Dispatcher.pure (D (M + 5))
        (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF])
        #[lit, .tuple #[.map S, acc]] = .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ SeenNamed S' lit ∧
      (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' := by
  obtain ⟨k, tag, l, rfl, -, sl⟩ := hlit
  obtain ⟨S', a', run, hS', named, sub, ha'⟩ := fetch_fold hM lines hl acc₀ l sl S acc hS ha
  refine ⟨S', a', ?_, hS', fun k' tag' l' e s ms => ?_, sub, ha'⟩
  · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-3-/2».pure]
    simpa [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-3-/4»] using run
  · obtain ⟨-, -, e₃⟩ := tuple3_inj e
    rw [← fieldsTerm_inj e₃] at ms
    exact named s ms

/-- `bdd_reduce/3` of `map_to_list_static/3` over a map BDD sees all its field keys. -/
theorem fetch_reduce {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) (acc₀ : Term)
    {b : Term} (wb : Bdd (MLit (level t (n + 1)).E) b) :
    ∀ (S : List (Term × Term)) (acc : Term), SeenOk S → AccOk t n lines acc₀ S acc →
      ∃ S' acc', Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b (.tuple #[.map S, acc])
          (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' ∧
        Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S' u) b := by
  refine Bdd.induction (P := fun ok b => (∀ u, ok u → MLit (level t (n + 1)).E u) →
      ∀ (S : List (Term × Term)) (acc : Term), SeenOk S → AccOk t n lines acc₀ S acc →
      ∃ S' acc', Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b (.tuple #[.map S, acc])
          (.function false "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S', acc']) ∧ SeenOk S' ∧ (∀ e ∈ S, e ∈ S') ∧ AccOk t n lines acc₀ S' acc' ∧
        Bdd (fun u => ok u ∧ SeenNamed S' u) b)
    ?_ ?_ ?_ ?_ (MLit (level t (n + 1)).E) b wb (fun _ h => h)
  · intro ok _ S acc hS ha
    exact ⟨S, acc, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, hS, fun e me => me, ha, by simp [Bdd]⟩
  · intro ok _ S acc hS ha
    exact ⟨S, acc, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, hS, fun e me => me, ha, by simp [Bdd]⟩
  · intro ok k x y okl lit S acc hS ha
    obtain ⟨S', a', run, hS', named, sub, ha'⟩ := fetch_leaf hM lines hl acc₀ (lit _ okl).1 S acc hS ha
    exact ⟨S', a', by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hS', sub, ha',
      Bdd.leaf_iff.mpr ⟨okl, named⟩⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits S acc hS ha
    have lits' : ∀ u, Above ok lit u → MLit (level t (n + 1)).E u := fun u hu => lits u hu.1
    obtain ⟨S₀, a₀, r₀, h₀, n₀, s₀, ha₀⟩ := fetch_leaf hM lines hl acc₀ (lits _ okl).1 S acc hS ha
    obtain ⟨S₁, a₁, r₁, h₁, s₁, ha₁, k₁⟩ := ic lits' S₀ a₀ h₀ ha₀
    obtain ⟨S₂, a₂, r₂, h₂, s₂, ha₂, k₂⟩ := iu lits' S₁ a₁ h₁ ha₁
    obtain ⟨S₃, a₃, r₃, h₃, s₃, ha₃, k₃⟩ := id lits' S₂ a₂ h₂ ha₂
    have t₀ : ∀ e ∈ S₀, e ∈ S₃ := fun e me => s₃ e (s₂ e (s₁ e me))
    refine ⟨S₃, a₃, ?_, h₃, fun e me => t₀ e (s₀ e me), ha₃, ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]
      simp [r₀, r₁, r₂, r₃]
    · have lift : ∀ (S' : List (Term × Term)), (∀ e ∈ S', e ∈ S₃) →
          ∀ u, (Above ok lit u ∧ SeenNamed S' u) → Above (fun u => ok u ∧ SeenNamed S₃ u) lit u :=
        fun S' sub u ⟨⟨o, lt⟩, nt⟩ => ⟨⟨o, seenNamed_mono sub nt⟩, lt⟩
      exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, seenNamed_mono t₀ n₀⟩,
        k₁.mono (lift S₁ fun e me => s₃ e (s₂ e me)), k₂.mono (lift S₂ fun e me => s₃ e me),
        k₃.mono (lift S₃ fun e me => me)⟩

end

end Elixir.STTDescrProofsTest.Nest

-- Putting a key into map types pops the key from the lines of their maps, unites the remaining maps, and stores
-- the key into every literal of the result, and into the open map that ends the paths without a positive literal.
namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map literals without a field at an atom key. -/
def Lacks (a : String) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    mapLookup l (.atom a) = none

/-- A literal without a field at a key holds a map with the key removed exactly when it allows the map at its other
keys. -/
theorem msemExcept_erase {tag : Term} {l : List (Term × Term)} {a : String} (la : mapLookup l (.atom a) = none)
    (w : MW V) : MSemExcept den tag l a w ↔ MSem den tag l (eraseK a w) := by
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨fun s => ?_, fun k i => by simpa [eraseK] using hd k i⟩
    by_cases e : s = a
    · subst e
      simp only [FSem, la, eraseK, ite_true]
      exact tagSem_none tag "atom"
    · have : (MKey.atom s) ≠ .atom a := fun h => e (MKey.atom.inj h)
      simpa [eraseK, this] using h s e
  · intro h
    refine ⟨fun s e => ?_, fun k i => by simpa [eraseK] using h.doms k i⟩
    have : (MKey.atom s) ≠ .atom a := fun h => e (MKey.atom.inj h)
    simpa [eraseK, this] using h s

/-- The field a put stores: a required value of a type. -/
theorem putField_sem {v : Term} (o : Option V) :
    FieldSem den (.tuple #[v, .atom "false"]) o ↔ ∃ x, o = some x ∧ den v x := by
  constructor
  · rintro ⟨t, opt, e, ⟨-, rfl⟩ | ⟨x, rfl, hx⟩⟩
    · simp [boolAtom] at e
    · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, -⟩ := e
      exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨v, Bool.false, rfl, Or.inr ⟨x, rfl, hx⟩⟩

/-- What a put stores at its key: some value of the type. -/
def PutAt (den : Term → V → Prop) (v : Term) (a : String) (w : MW V) : Prop := ∃ x, w (.atom a) = some x ∧ den v x

theorem putFieldV {v : Term} (hv : E v) : FieldValue E (.tuple #[v, .atom "false"]) := ⟨v, Bool.false, rfl, hv⟩

/-- `map_put_key_leaf/4` stores a required field into a literal without the key: its maps are those of the literal
with the key set to a value of the type. -/
theorem put_leaf (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) {lit : Term} (hl : MLit E lit)
    (la : Lacks a lit) :
    ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» lit (.atom a) v (.atom "false") = .ok lit' ∧
      MLit E lit' ∧ IsLeaf lit' ∧
      ∀ w, valM E den w lit' = (valM E den (eraseK a w) lit && bp (PutAt den v a w)) := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, -, -⟩ := hl
  have lka := la k tag l rfl
  obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef g sl a (putFieldV hv)
  refine ⟨_, ?_, ml', ⟨k', tag, fieldsTerm l', rfl⟩, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
    simp [runS, leaf]
  · apply Bool.eq_iff_iff.mpr
    rw [sem w, Bool.and_eq_true, valM_leaf ef sl g, bp_true, putField_sem, ← msemExcept_erase lka]
    rfl

/-- `map_put_key_leaf/4` stores a required field into the top literal: its maps are those with the key set to a value
of the type. -/
theorem put_top (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) (k : Int := 61102469) :
    ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» (.tuple #[.integer k, .atom "open", .nil]) (.atom a)
        v (.atom "false") = .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = bp (PutAt den v a w) := by
  have sl : FieldsV E [] := ⟨by simp, by simp⟩
  obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef (Or.inl rfl) sl a (putFieldV hv)
  refine ⟨_, ?_, ml', ⟨k', .atom "open", fieldsTerm l', rfl⟩, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
    have e : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
    rw [e] at runS
    simp [runS, leaf]
  · apply Bool.eq_iff_iff.mpr
    rw [sem w, bp_true, putField_sem]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun s _ => Or.inl rfl, fun k i => Or.inl rfl⟩, h⟩⟩

/-- What `map_put_key_leaf/4` does with a value and an optional flag: on literals without the key, the new literal
holds the maps of the literal with the key removed and that `P` accepts; on the top literal, the maps `P` accepts. -/
structure LeafPut (E : Term → Prop) (den : Term → V → Prop) (a : String) (v ov : Term) (P : MW V → Prop) : Prop where
  leaf : ∀ {lit}, MLit E lit → Lacks a lit → ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» lit (.atom a) v ov =
    .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = (valM E den (eraseK a w) lit && bp (P w))
  top : ∀ k : Int, ∃ lit', Elixir.Module.Types.Descr.«map_put_key_leaf/4» (.tuple #[.integer k, .atom "open", .nil])
    (.atom a) v ov = .ok lit' ∧ MLit E lit' ∧ IsLeaf lit' ∧ ∀ w, valM E den w lit' = bp (P w)

/-- Puts store a required field of a type. -/
theorem leafPut_put (ef : EF nd E V den tl K) (a : String) {v : Term} (hv : E v) :
    LeafPut E den a v (.atom "false") (PutAt den v a) :=
  ⟨fun hl la => put_leaf ef a hv hl la, fun k => put_top ef a hv k⟩

/-- The field a deletion stores: an absent key. -/
theorem delField_sem (ef : EF nd E V den tl K) (o : Option V) :
    FieldSem den (.tuple #[.map [], .atom "true"]) o ↔ o = none := by
  rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]
  constructor
  · rintro (⟨h, -⟩ | ⟨x, rfl, hx⟩)
    · exact h
    · exact absurd (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩)
        ((none_field (den := den) ef).2 (some x))
  · intro h; exact Or.inl ⟨h, rfl⟩

/-- Deletions remove the key: closed literals already lack it, others store an absent field. -/
theorem leafPut_del (ef : EF nd E V den tl K) (a : String) :
    LeafPut E den a (.map []) (.atom "true") (fun w => w (.atom a) = none) where
  leaf := by
    intro lit hl la
    obtain ⟨⟨k, tag, l, rfl, g, sl⟩, ntop, key⟩ := hl
    have lka := la k tag l rfl
    have hd : FieldValue E (.tuple #[.map [], .atom "true"]) := ⟨.map [], Bool.true, rfl, ef.none⟩
    by_cases closed : tag = .atom "closed"
    · subst closed
      refine ⟨_, ?_, ⟨⟨k, _, l, rfl, g, sl⟩, ntop, key⟩, ⟨k, _, _, rfl⟩, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
        simp [Erlang.erlang.«==/2»]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.and_eq_true, valM_leaf ef sl g, valM_leaf ef sl g, bp_true, msem_split_absent ef g lka,
          fieldSem_tagV ef.mopsE ef.mdopsE ef.semR g, tagSem_atom, ← msemExcept_erase lka]
        simp
    · obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef g sl a hd
      refine ⟨_, ?_, ml', ⟨k', tag, fieldsTerm l', rfl⟩, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
        rcases g with rfl | rfl | ⟨dl, rfl, -⟩
        · simp [runS, leaf]
        · exact absurd rfl closed
        · have ne := fieldsTerm_ne_atom dl "closed"
          generalize fieldsTerm dl = T at ne runS leaf ⊢
          split
          · rename_i h₁ _; exact absurd (tuple3_inj h₁).2.1 ne
          · simp [runS, leaf]
      · apply Bool.eq_iff_iff.mpr
        rw [sem w, Bool.and_eq_true, valM_leaf ef sl g, bp_true, delField_sem ef, ← msemExcept_erase lka]
  top := by
    intro k
    have sl : FieldsV E [] := ⟨by simp, by simp⟩
    have hd : FieldValue E (.tuple #[.map [], .atom "true"]) := ⟨.map [], Bool.true, rfl, ef.none⟩
    obtain ⟨k', l', runS, leaf, ml', sem⟩ := store_leaf (den := den) ef (Or.inl rfl) sl a hd
    refine ⟨_, ?_, ml', ⟨k', .atom "open", fieldsTerm l', rfl⟩, fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_put_key_leaf/4»
      have e : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
      rw [e] at runS
      simp [runS, leaf]
    · apply Bool.eq_iff_iff.mpr
      rw [sem w, bp_true, delField_sem ef]
      exact ⟨fun h => h.2, fun h => ⟨⟨fun s _ => Or.inl rfl, fun k i => Or.inl rfl⟩, h⟩⟩

/-- `map_put_key_before?/2` checks that a literal comes before every literal of a BDD, by its head. -/
theorem put_before {ok : Term → Prop} {b : Term} (wb : Bdd ok b) (lit : Term) :
    Elixir.Module.Types.Descr.«map_put_key_before?/2» lit b =
      .ok (boolAtom (bp (∀ l, head b = some l → compare (fuel lit l) lit l = .lt))) := by
  unfold Elixir.Module.Types.Descr.«map_put_key_before?/2»
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, l, c, u, d, rfl⟩
  · simp [Lynx.Term.isMember, head, boolAtom]
  · simp [Lynx.Term.isMember, head, boolAtom]
  · by_cases e : compare (fuel lit (.tuple #[.integer k, x, y])) lit (.tuple #[.integer k, x, y]) = .lt
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.true]
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.false,
        Ordering.isLT_iff_eq_lt]
  · by_cases e : compare (fuel lit l) lit l = .lt
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.true]
    · simp [Lynx.Term.isMember, head, boolAtom, Erlang.erlang.«</2», e, Term.false,
        Ordering.isLT_iff_eq_lt]

/-- What `map_put_key_bdd/5` guarantees on a BDD: the result is an ordered BDD of literals whose maps, among those
whose key holds a value of the type, are the maps of the BDD with the key removed. Without a positive literal on the
path, it holds no other maps. -/
def PutBdd (E : Term → Prop) (den : Term → V → Prop) (a : String) (v ov : Term) (P : MW V → Prop) (r : Term)
    (p : Bool) : Prop :=
  ∃ r', Elixir.Module.Types.Descr.«map_put_key_bdd/5» r (.atom a) v ov (boolAtom p) = .ok r' ∧
    Bdd (MLit E) r' ∧ ∀ w : MW V,
      (P w → eval (valM E den w) r' = eval (valM E den (eraseK a w)) r) ∧
      (p = Bool.false → ¬P w → eval (valM E den w) r' = Bool.false)

/-- The node `map_put_key_bdd/5` builds from a stored literal and the stored children, either as is or with BDD
operations, holds the propositional node of its parts. -/
theorem put_node {lit c u d : Term} (ml : MLit E lit) (il : IsLeaf lit) (wc : Bdd (MLit E) c) (wu : Bdd (MLit E) u)
    (wd : Bdd (MLit E) d) (B : Term) (hB : B = boolAtom (bp ((∀ l, head c = some l → compare (fuel lit l) lit l = .lt) ∧
      (∀ l, head u = some l → compare (fuel lit l) lit l = .lt) ∧ (∀ l, head d = some l → compare (fuel lit l) lit l = .lt)))) :
    ∃ r, ((fun {lynxValue : Type}
            (lynxBody : (Unit → Except Lynx.Exception lynxValue) → Except Lynx.Exception lynxValue)
            (lynxNext : Unit → Except Lynx.Exception lynxValue) => lynxBody lynxNext)
          (fun lynxMatchNext =>
            match B with
            | _v_3 =>
              Lynx.Except.guard (Except.ok (Lynx.Term.isMember B [Lynx.Term.atom "false", Lynx.Term.atom "nil"]))
                (fun _ => do
                  let _17 ← Elixir.Module.Types.Descr.«bdd_intersection/2» lit c
                  let _18 ← Elixir.Module.Types.Descr.«bdd_union/2» _17 u
                  let _16 ← Elixir.Module.Types.Descr.«bdd_difference/2» d lit
                  Elixir.Module.Types.Descr.«bdd_union/2» _18 _16)
                lynxMatchNext)
          (fun (_ : Unit) => match B with | _29 => Elixir.Module.Types.Descr.«bdd_node_new/4» lit c u d)) = .ok r ∧
      Bdd (MLit E) r ∧ ∀ w : MW V, eval (valM E den w) r =
        ((valM E den w lit && eval (valM E den w) c) || eval (valM E den w) u || (!valM E den w lit && eval (valM E den w) d)) := by
  have wl : Bdd (MLit E) lit := by obtain ⟨k, x, y, rfl⟩ := il; exact Bdd.leaf_iff.mpr ml
  by_cases ord : (∀ l, head c = some l → compare (fuel lit l) lit l = .lt) ∧
      (∀ l, head u = some l → compare (fuel lit l) lit l = .lt) ∧ (∀ l, head d = some l → compare (fuel lit l) lit l = .lt)
  · rw [bp_true.mpr ord] at hB
    subst hB
    obtain ⟨h, run⟩ := node_new lit c u d il wc wu wd
    refine ⟨.tuple #[.integer h, lit, c, u, d], ?_, ?_, fun w => by simp⟩
    · simp [Lynx.Term.isMember, boolAtom, run]
    · obtain ⟨k, x, y, rfl⟩ := il
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ml, wc.raise ord.1, wu.raise ord.2.1, wd.raise ord.2.2⟩
  · rw [bp_false.mpr ord] at hB
    subst hB
    obtain ⟨i, ri, oi, si⟩ := inter_ok wl wc
    obtain ⟨j, rj, oj, sj⟩ := union_ok (oi _ wl wc) wu
    obtain ⟨e, re, oe, se⟩ := diff_ok wd wl
    obtain ⟨r, rr, or_, sr⟩ := union_ok (oj _ (oi _ wl wc) wu) (oe _ wd wl)
    refine ⟨r, ?_, or_ _ (oj _ (oi _ wl wc) wu) (oe _ wd wl), fun w => ?_⟩
    · simp [Lynx.Term.isMember, boolAtom, ri, rj, re, rr]
    · have resp := valM_resp (E := E) (den := den) w
      obtain ⟨k, x, y, rfl⟩ := il
      rw [sr _ resp, sj _ resp, si _ resp, se _ resp]
      simp only [eval_leaf]
      cases valM E den w (.tuple #[.integer k, x, y]) <;> simp

/-- `map_put_key_bdd/5` on ordered BDDs of literals without the key. -/
theorem put_bdd (a : String) {v ov : Term} {P : MW V → Prop} (lp : LeafPut E den a v ov P) :
    ∀ (ok : Term → Prop) (r : Term), Bdd ok r → (∀ t, ok t → MLit E t ∧ Lacks a t) → ∀ p,
      PutBdd E den a v ov P r p := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MLit E t ∧ Lacks a t) → ∀ p, PutBdd E den a v ov P r p)
    ?_ ?_ ?_ ?_
  · intro ok _ p
    cases p
    · obtain ⟨lit', run, ml', il', sem⟩ := lp.top 61102469
      refine ⟨lit', ?_, by obtain ⟨k, x, y, rfl⟩ := il'; exact Bdd.leaf_iff.mpr ml', fun w => ⟨fun h => ?_, fun _ h => ?_⟩⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», boolAtom, run]
      · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
      · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
    · refine ⟨.atom "bdd_top", ?_, Bdd.top, fun w => ⟨fun _ => by simp, fun h => by cases h⟩⟩
      simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», boolAtom]
  · intro ok _ p
    refine ⟨.atom "bdd_bot", ?_, Bdd.bot, fun w => ⟨fun _ => by simp, fun _ _ => by simp⟩⟩
    simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5»]
  · intro ok k x y okl hok p
    obtain ⟨ml, la⟩ := hok _ okl
    obtain ⟨lit', run, ml', il', sem⟩ := lp.leaf ml la
    refine ⟨lit', ?_, by obtain ⟨k, x, y, rfl⟩ := il'; exact Bdd.leaf_iff.mpr ml', fun w => ⟨fun h => ?_, fun _ h => ?_⟩⟩
    · simp [Elixir.Module.Types.Descr.«map_put_key_bdd/5», run]
    · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
    · obtain ⟨k, x, y, rfl⟩ := il'; simp [sem, h]
  · intro ok h lit c u d il okl _ _ _ ic iu id hok p
    obtain ⟨ml, la⟩ := hok _ okl
    have hok' : ∀ t, Above ok lit t → MLit E t ∧ Lacks a t := fun t ht => hok t ht.1
    obtain ⟨lit', rl, ml', il', sl⟩ := lp.leaf ml la
    obtain ⟨c', rc, wc, sc⟩ := ic hok' Bool.true
    obtain ⟨u', ru, wu, su⟩ := iu hok' p
    obtain ⟨d', rd, wd, sd⟩ := id hok' p
    have bc := put_before wc lit'
    have bu := put_before wu lit'
    have bd := put_before wd lit'
    obtain ⟨r, rr, wr, sr⟩ := put_node (den := den) ml' il' wc wu wd _ rfl
    refine ⟨r, ?_, wr, fun w => ⟨fun hw => ?_, fun hp hw => ?_⟩⟩
    · have rc' : Elixir.Module.Types.Descr.«map_put_key_bdd/5» c (.atom a) v ov (.atom "true") = .ok c' := rc
      rw [Elixir.Module.Types.Descr.«map_put_key_bdd/5».eq_def]
      simp only [rl, rc', ru, rd, bu, bd, bc, Lynx.Except.ok_bind]
      rw [← rr]
      rw [← bp_and, ← bp_and]
      generalize bp (∀ l, head c' = some l → compare (fuel lit' l) lit' l = .lt) = x
      generalize bp (∀ l, head u' = some l → compare (fuel lit' l) lit' l = .lt) = y
      generalize bp (∀ l, head d' = some l → compare (fuel lit' l) lit' l = .lt) = z
      cases x <;> cases y <;> cases z <;> simp [boolAtom]
    · rw [sr w, sl w, (sc w).1 hw, (su w).1 hw, (sd w).1 hw, eval_node]
      simp [bp_true.mpr hw]
    · rw [sr w, sl w, (su w).2 hp hw, (sd w).2 hp hw]
      simp [bp_false.mpr hw]

theorem field_union_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_union/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∨ FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.union h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_union/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.orElse]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x =>
      simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or, sem x]

/-- `map_pair_projection_keeps_full_snd?/2` checks for a value at the key outside every negated pair. -/
theorem mkeeps_snd (ef : EF nd E V den tl K) {m : Nat} (hm : K + 4 ≤ m) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {field : Term} (hf : FieldValue E field) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (m + 1)) (Term.list P) field =
        .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ o, FieldSem den field o ∧ ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → ¬FieldSem den f o) := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel_at (m := m + 1) "Elixir.Module.Types.Descr"
    "-map_pair_projection_keeps_full_snd?/2-fun-0-" #[]
    (fun pre a => FieldValue E a ∧ ∀ o, FieldSem den a o ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, hf', -⟩ := hP x mx
      obtain ⟨r, tr, run, sr⟩ := field_union_val (den := den) ef (m := m) (by omega) hf' ta
      refine ⟨r, ⟨tr, fun o => ?_⟩, ?_⟩
      · rw [sr, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_pair_projection_keeps_full_snd?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_pair_projection_keeps_full_snd?/2-fun-0-/2»] using run)
    (.tuple #[.map [], .atom "false"]) ⟨(none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o]⟩
  obtain ⟨d, td, rd, sd⟩ := field_diff_val (den := den) ef (m := m + 1) (by omega) hf tu
  obtain ⟨e, re, se⟩ := field_empty_val (den := den) ef (m := m + 1) (by omega) td
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2», run, rd, re,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨o, ho⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [Classical.not_not, sd, su] at ho
      exact ⟨o, ho.1, fun p mp f nb e hfo => ho.2 ⟨p, mp, f, nb, e, hfo⟩⟩
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro o ho none
      refine (se.mp rfl) o ((sd o).mpr ⟨ho, fun h => ?_⟩)
      obtain ⟨p, mp, f, b, e, hfo⟩ := (su o).mp h
      exact none p mp f b e hfo

/-- Map literals without a key. -/
def LitA (E : Term → Prop) (a : String) (t : Term) : Prop := MLit E t ∧ Lacks a t

theorem lacks_lit {k : Int} {tag : Term} {l : List (Term × Term)} {a : String} (la : mapLookup l (.atom a) = none) :
    Lacks a (.tuple #[.integer k, tag, fieldsTerm l]) := by
  intro k' tag' l' e
  obtain ⟨-, -, e₃⟩ := tuple3_inj e
  rw [← fieldsTerm_inj e₃]
  exact la

/-- Map types of one literal without a key. -/
theorem oField_litA {k : Int} {tag : Term} {l : List (Term × Term)} {a : String}
    (h : MField E (.tuple #[.integer k, tag, fieldsTerm l])) (la : mapLookup l (.atom a) = none) :
    OField (LitA E a) (.tuple #[.integer k, tag, fieldsTerm l]) := by
  rcases h with top | wb
  · exact Or.inl top
  · exact Or.inr (Bdd.leaf_iff.mpr ⟨Bdd.leaf_iff.mp wb, lacks_lit la⟩)

/-- The rest of a pair. -/
def pairSnd : Term → Term
  | .tuple ⟨[_, b]⟩ => b
  | _ => .nil

/-- One step of `map_dnf_pop_key/2`: the map types of the maps of a non-empty line without a key, as maps whose key
may hold anything. -/
theorem mline_pop (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {L : Term} (hL : MLine E L)
    (ne : ∃ w, InMLine den L w) :
    ∃ Bs : List Term, (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a])
        #[L] = .ok (Term.list Bs) ∧ (∀ b ∈ Bs, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ Bs, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, -⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, -⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  have key : ∀ w o, MSem den tag l (setK a o w) ↔
      FieldSem den (fieldAt tag l a) o ∧ denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) =
        Bool.true := by
    intro w o
    rw [msem_at ef g l a, rest, eraseK_setK]
    simp [setK]
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_pop_key/2-fun-1-/1».pure]
  by_cases nn : negs = []
  · subst nn
    refine ⟨[.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]], ?_, by simpa using ⟨hb, orest⟩, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run, Term.list]
    · constructor
      · rintro ⟨b', mb, hb'⟩
        rw [List.mem_singleton] at mb; subst mb
        exact ⟨w₀ (.atom a), inMLine_iff.mpr ⟨(key w _).mpr ⟨split₀.1, hb'⟩, by simp⟩⟩
      · rintro ⟨o, ho⟩
        exact ⟨_, List.mem_singleton_self _, ((key w o).mp (inMLine_iff.mp ho).1).2⟩
  obtain ⟨N₀, negs₀, rfl⟩ : ∃ N₀ negs₀, negs = N₀ :: negs₀ := by
    cases negs with
    | nil => exact absurd rfl nn
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a (N₀ :: negs₀) lits []
  all_goals have rr' := rr; simp only [Term.list] at rr'
  · refine ⟨[], ?_, by simp, fun w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
        Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', Term.list]
    · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists]
      intro o hw
      exact (inMLine_iff.mp hw).2 N mN (hN _)
  simp only [List.append_nil] at rr
  have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr split₀.2⟩
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  -- Values at the key of maps of the line, with the rest of a map.
  have line : ∀ w o, InMLine den (.tuple #[tag, fieldsTerm l, Term.list (N₀ :: negs₀)]) (setK a o w) ↔
      FieldSem den (fieldAt tag l a) o ∧
        denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) = Bool.true ∧
        ∀ p ∈ P, ¬MPairIn E den p o (eraseK a w) := by
    intro w o
    rw [inMLine_iff, key, and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h p mp hp => ?_, fun h N mN hN' => ?_⟩)
    · obtain ⟨N, mN, hN'⟩ := (sP (setK a o w)).mpr ⟨p, mp, by simpa [setK, eraseK_setK] using hp⟩
      exact h N mN hN'
    · obtain ⟨p, mp, hp⟩ := (sP (setK a o w)).mp ⟨N, mN, hN'⟩
      exact h p mp (by simpa [setK, eraseK_setK] using hp)
  obtain ⟨s, rs, ss⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hf
  cases s
  · obtain ⟨Q, rQ, qQ, kQ, fQ, sQ⟩ := mproject_pairs ef hn P hP' hf hb restNe
    have fQ := fQ ⟨_, split₀.1⟩
    refine ⟨Q.map pairSnd, ?_, fun b' mb => ?_, fun w => ?_⟩
    · have rm := map_list (Dispatcher.ofTable Erlang.program.fun_table (n + 2)) "Elixir.Module.Types.Descr"
        "-map_dnf_pop_key/2-fun-0-" #[] pairSnd Q fun q mq => by
          obtain ⟨f', b', rfl, -⟩ := qQ q mq
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_pop_key/2-fun-0-/1».pure]
          simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-0-/1», Erlang.erlang.«element/2», pairSnd]
      cases P with
      | nil => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, rQ, rm, Lynx.Term.isMember, boolAtom, Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, rQ, rm, Lynx.Term.isMember, boolAtom, Term.list]
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mb
      obtain ⟨f', b'', rfl, -, fb, -⟩ := qQ q mq
      obtain ⟨f₂, b₂, e, ob⟩ := kQ (LitA E a) orest kP _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨-, rfl⟩ := e
      exact ⟨fb, ob⟩
    · constructor
      · rintro ⟨b', mb, hb'⟩
        obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mb
        obtain ⟨f', b'', rfl, o, ho⟩ := fQ q mq
        obtain ⟨hy, hr, hout⟩ := (sQ o (eraseK a w)).mp ⟨_, mq, mpairIn_iff.mpr ⟨ho, hb'⟩⟩
        exact ⟨o, (line w o).mpr ⟨hy, hr, hout⟩⟩
      · rintro ⟨o, ho⟩
        obtain ⟨q, mq, hq⟩ := (sQ o (eraseK a w)).mpr ((line w o).mp ho)
        obtain ⟨f', b'', rfl, -, hb'⟩ := hq
        exact ⟨b'', List.mem_map.mpr ⟨_, mq, rfl⟩, hb'⟩
  · obtain ⟨o₀, ho₀, out₀⟩ := ss.mp rfl
    refine ⟨[.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]], ?_, by simpa using ⟨hb, orest⟩, fun w => ?_⟩
    · cases P with
      | nil => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, Lynx.Term.isMember, boolAtom, Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«-map_dnf_pop_key/2-fun-1-/2», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rs, Lynx.Term.isMember, boolAtom, Term.list]
    · constructor
      · rintro ⟨b', mb, hb'⟩
        rw [List.mem_singleton] at mb; subst mb
        refine ⟨o₀, (line w o₀).mpr ⟨ho₀, hb', fun p mp hp => ?_⟩⟩
        obtain ⟨f', nb, e, hf', -⟩ := hp
        exact out₀ p mp f' nb e hf'
      · rintro ⟨o, ho⟩
        exact ⟨_, List.mem_singleton_self _, ((line w o).mp ho).2.1⟩

/-- Merging literals at one of their keys keeps literals without another key. -/
theorem mergeOk_litA (a : String) : MergeOk E (LitA E a) := by
  intro k₁ k tag l₁ l s ⟨_, la⟩ hs look ml
  refine ⟨ml, lacks_lit ?_⟩
  have la₁ := la k₁ tag l₁ rfl
  have ne : s ≠ a := fun e => hs (e ▸ la₁)
  rw [look a ne, la₁]

/-- `map_union_pairs/1` unites map types two by two. -/
theorem munion_list (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {ok : Term → Prop} (mok : MergeOk E ok) :
    ∀ Bs : List Term, (∀ b ∈ Bs, MField E b ∧ OField ok b) →
      ∃ Cs : List Term, Elixir.Module.Types.Descr.«map_union_pairs/1» (D m) (Term.list Bs) = .ok (Term.list Cs) ∧
        Cs.length ≤ Bs.length ∧ (2 ≤ Bs.length → Cs.length < Bs.length) ∧
        (∀ c ∈ Cs, MField E c ∧ OField ok c) ∧
        ∀ w : MW V, (∃ c ∈ Cs, denMF E den c w = Bool.true) ↔ ∃ b ∈ Bs, denMF E den b w = Bool.true
  | [] , _ => ⟨[], by simp [Elixir.Module.Types.Descr.«map_union_pairs/1», Term.list], by simp, by simp, by simp,
      fun w => by simp⟩
  | [b], hb => ⟨[b], by simp [Elixir.Module.Types.Descr.«map_union_pairs/1», Term.list], by simp, by simp, hb,
      fun w => Iff.rfl⟩
  | b₁ :: b₂ :: Bs, hB => by
    obtain ⟨f₁, o₁⟩ := hB b₁ (by simp)
    obtain ⟨f₂, o₂⟩ := hB b₂ (by simp)
    obtain ⟨c, rc, fc, kc, sc⟩ := opt_map_union_sem (den := den) ef hm f₁ f₂ []
    obtain ⟨Cs, rCs, len, -, hCs, sCs⟩ := munion_list ef hm mok Bs fun b mb => hB b (by simp [mb])
    refine ⟨c :: Cs, ?_, by simp; omega, fun _ => by simp; omega, fun c' mc => ?_, fun w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_union_pairs/1».eq_def]
      simp [Term.list, rc, rCs]
    · rcases List.mem_cons.mp mc with rfl | mc
      · exact ⟨fc, kc ok mok o₁ o₂⟩
      · exact hCs c' mc
    · simp only [List.mem_cons, exists_eq_or_imp] at sCs ⊢
      rw [sc, Bool.or_eq_true, sCs]
      exact or_assoc

/-- `map_union_all/1` unites map types. -/
theorem munion_all (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {ok : Term → Prop} (mok : MergeOk E ok) :
    ∀ (n : Nat) (Bs : List Term), Bs.length ≤ n → (∀ b ∈ Bs, MField E b ∧ OField ok b) →
      ∃ r, Elixir.Module.Types.Descr.«map_union_all/1» (D m) (Term.list Bs) = .ok r ∧ MField E r ∧ OField ok r ∧
        ∀ w : MW V, denMF E den r w = Bool.true ↔ ∃ b ∈ Bs, denMF E den b w = Bool.true
  | n, [], _, _ => ⟨.atom "bdd_bot", by rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]; rfl, Or.inr Bdd.bot,
      Or.inr Bdd.bot, fun w => by simp [denMF_bot]⟩
  | n, [b], _, hb => by
    obtain ⟨fb, ob⟩ := hb b (by simp)
    exact ⟨b, by rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]; rfl, fb, ob, fun w => by simp⟩
  | n + 1, b₁ :: b₂ :: Bs, len, hB => by
    obtain ⟨Cs, rCs, -, shorter, hCs, sCs⟩ := munion_list (den := den) ef hm mok (b₁ :: b₂ :: Bs) hB
    have := shorter (by simp)
    obtain ⟨r, rr, fr, kr, sr⟩ := munion_all ef hm mok n Cs (by simp at len this; omega) hCs
    refine ⟨r, ?_, fr, kr, fun w => (sr w).trans (sCs w)⟩
    rw [Elixir.Module.Types.Descr.«map_union_all/1».eq_def]
    simp only [Term.list] at rCs ⊢
    simp [rCs, rr]
  | 0, _ :: _ :: _, len, _ => by simp at len

/-- `map_dnf_pop_key/2` on non-empty lines: a map type without the key whose maps, with the key removed, are the
maps of the lines with the key changed to anything. -/
theorem mdnf_pop (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ r, Elixir.Module.Types.Descr.«map_dnf_pop_key/2» (D (n + 3)) (Term.list lines) (.atom a) = .ok r ∧
      MField E r ∧ OField (LitA E a) r ∧
      ∀ w, denMF E den r (eraseK a w) = Bool.true ↔ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
  classical
  have each : ∀ L ∈ lines, ∃ Bs : List Term,
      (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a]) #[L] =
        .ok (Term.list Bs) ∧ (∀ b ∈ Bs, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ Bs, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) :=
    fun L mL => mline_pop ef hn a (hl L mL).1 (hl L mL).2
  let h : Term → List Term := fun L => if hL : L ∈ lines then Classical.choose (each L hL) else []
  have hh : ∀ L ∈ lines,
      (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" 1 #[.atom a]) #[L] =
        .ok (Term.list (h L)) ∧ (∀ b ∈ h L, MField E b ∧ OField (LitA E a) b) ∧
      ∀ w, (∃ b ∈ h L, denMF E den b (eraseK a w) = Bool.true) ↔ ∃ o, InMLine den L (setK a o w) := fun L mL => by
    simp only [h, dite_eq_left mL]
    exact Classical.choose_spec (each L mL)
  have fm := flatmap_lists (m := n + 3) "Elixir.Module.Types.Descr" "-map_dnf_pop_key/2-fun-1-" #[.atom a] h lines
    fun L mL => (hh L mL).1
  obtain ⟨r, rr, fr, kr, sr⟩ := munion_all (den := den) ef (m := n + 3) (by omega) (mergeOk_litA a) _
    (lines.flatMap h) (Nat.le_refl _) fun b mb => by
      obtain ⟨L, mL, mb⟩ := List.mem_flatMap.mp mb
      exact (hh L mL).2.1 b mb
  refine ⟨r, ?_, fr, kr, fun w => ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_dnf_pop_key/2», fm, rr]
  · rw [sr]
    constructor
    · rintro ⟨b, mb, hb⟩
      obtain ⟨L, mL, mb⟩ := List.mem_flatMap.mp mb
      exact ⟨L, mL, ((hh L mL).2.2 w).mp ⟨b, mb, hb⟩⟩
    · rintro ⟨L, mL, hL⟩
      obtain ⟨b, mb, hb⟩ := ((hh L mL).2.2 w).mpr hL
      exact ⟨b, List.mem_flatMap.mpr ⟨L, mL, mb⟩, hb⟩

/-- The force clause of `map_update_named_key/5` for a constant: the maps of the lines with the key set to a value of
the type. -/
theorem put_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term} {P : MW V → Prop}
    (lp : LeafPut E den a v ov P) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ bdds : List Term, (∀ (ow : Bool) (Fo : Term),
        (ow = Bool.true → Elixir.Module.Types.Descr.«map_dnf_fetch_static/2» (D (n + 3)) (Term.list lines) (.atom a) =
          .ok Fo) →
        Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "true")
          (boolAtom ow) = .ok (.tuple #[Term.list bdds, if ow then Fo else .atom "nil"])) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) := by
  obtain ⟨r, rr, -, kr, sr⟩ := mdnf_pop ef hn a lines hl
  rcases kr with ⟨k, rfl⟩ | wr
  · obtain ⟨lit', run, ml', il', sem⟩ := lp.top k
    refine ⟨[lit'], fun ow Fo hF => ?_, fun b mb => by
      rw [List.mem_singleton] at mb; subst mb; obtain ⟨k', x, y, rfl⟩ := il'; exact Or.inr (Bdd.leaf_iff.mpr ml'),
      fun w => ?_⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5»,
          run, Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5»,
          run, Lynx.Term.isMember, Term.list, boolAtom, hF rfl]
    · obtain ⟨k', x, y, rfl⟩ := il'
      have top := (sr w).mp (by simp [denMF_top])
      simp only [List.mem_singleton, exists_eq_left]
      rw [denMF_bdd (Bdd.leaf_iff.mpr ml'), eval_leaf, sem, bp_true]
      exact ⟨fun h => ⟨h, top⟩, fun h => h.1⟩
  obtain ⟨r', run, wr', sem⟩ := put_bdd a lp _ r wr (fun _ h => h) Bool.false
  have wr₀ : Bdd (MLit E) r := wr.mono fun _ h => h.1
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    refine ⟨[], fun ow Fo hF => ?_, by simp, fun w => ?_⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, Lynx.Term.isMember, Term.list, boolAtom, hF rfl]
    · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro _ h
      have := (sr w).mpr h
      simp [denMF_bot] at this
  refine ⟨[r'], fun ow Fo hF => ?_, fun b mb => by rw [List.mem_singleton] at mb; subst mb; exact Or.inr wr',
    fun w => ?_⟩
  · have run' : Elixir.Module.Types.Descr.«map_put_key_bdd/5» r (.atom a) v ov (.atom "false") = .ok r' := run
    rcases wr₀.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom,
          hF rfl]
    · exact absurd rfl bot
    all_goals
      cases ow
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom]
      · simp [Elixir.Module.Types.Descr.«map_update_named_key/5», rr, run', Lynx.Term.isMember, Term.list, boolAtom,
          hF rfl]
  · simp only [List.mem_singleton, exists_eq_left]
    rw [denMF_bdd wr', ← sr, denMF_bdd wr₀]
    by_cases hp : P w
    · rw [(sem w).1 hp]; simp [hp]
    · rw [(sem w).2 rfl hp]; simp [hp]

/-- What a put of a constant gives: a map type of the maps of the lines with the key set to a value of the type, or the
empty type. -/
def PutMaps (E : Term → Prop) (den : Term → V → Prop) (a : String) (P : MW V → Prop) (lines : List Term) (Y : Term) :
    Prop :=
  ∃ r, MField E r ∧ (Y = .map [(.atom "map", r)] ∨ (Y = .map [] ∧ ∀ w, denMF E den r w = Bool.false)) ∧
    ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w)

theorem put_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term}
    {P : MW V → Prop} (lp : LeafPut E den a v ov P) (bdd : Term) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") (.atom "true") =
        .ok (.tuple #[.map [], Y, .nil, .atom "true"]) ∧ PutMaps E den a P lines Y := by
  obtain ⟨bdds, rb, fb, sb⟩ := put_lines ef hn a lp lines hl
  have rb : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "true") (.atom "false") =
      .ok (.tuple #[Term.list bdds, .atom "nil"]) := by simpa [boolAtom] using rb Bool.false .nil (by simp)
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[.map [], .nil, .nil, .atom "false"])
      (Term.list lines) (.cons (.atom a) .nil) (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"])
      (.atom "true") (.atom "true") (.atom "false") (.atom "true") =
      .ok (.tuple #[.map [], Term.list bdds, .nil, .atom "true"]) := by
    have rb' := rb
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb']
    rw [show (Term.nil) = Term.list [] from rfl, append_list]
    simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"])
      (.atom "false") (.atom "true") (.atom "false") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list, Term.properList?, nk₁,
    nk₂]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have sem : ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) :=
    fun w => (sr w).trans (sb w)
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    refine ⟨.map [], by simp [rr], .atom "bdd_bot", fr, Or.inr ⟨rfl, fun w => denMF_bot w⟩, sem⟩
  · refine ⟨.map [(.atom "map", r)], ?_, r, fr, Or.inl rfl, sem⟩
    simp only [rr, Lynx.Except.ok_bind]

/-- What a put of a constant gives on a map field: the maps of the field with the key set to a value of the type. -/
def PutField (E : Term → Prop) (den : Term → V → Prop) (a : String) (P : MW V → Prop) (b Y : Term) : Prop :=
  ∃ r, MField E r ∧ (Y = .map [(.atom "map", r)] ∨ (Y = .map [] ∧ ∀ w, denMF E den r w = Bool.false)) ∧
    ∀ w, denMF E den r w = Bool.true ↔ P w ∧ ∃ o, denMF E den b (setK a o w) = Bool.true

theorem putMaps_field {a : String} {P : MW V → Prop} {b Y : Term} {lines : List Term}
    (inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (h : PutMaps E den a P lines Y) :
    PutField E den a P b Y := by
  obtain ⟨r, fr, hY, sr⟩ := h
  refine ⟨r, fr, hY, fun w => (sr w).trans (and_congr Iff.rfl ⟨?_, ?_⟩)⟩
  · rintro ⟨L, mL, o, hL⟩; exact ⟨o, (inB _).mpr ⟨L, mL, hL⟩⟩
  · rintro ⟨o, ho⟩; obtain ⟨L, mL, hL⟩ := (inB _).mp ho; exact ⟨L, mL, o, hL⟩

/-- `map_update_static/5` puts a constant into a map field: `:badmap` when it is empty. -/
theorem put_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v ov : Term}
    {P : MW V → Prop} (lp : LeafPut E den a v ov P)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ Y, res = .tuple #[.map [], Y, .nil, .atom "true"] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          PutField E den a P b Y) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨Y, rY, pY⟩ := put_static_dnf ef hn a lp (.tuple #[.integer k, tag, fieldsTerm l]) _ hl
      refine ⟨_, ?_, Or.inr ⟨Y, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, putMaps_field (fun w => ?_) pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨Y, rY, pY⟩ := put_static_dnf ef hn a lp b (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨Y, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, putMaps_field inB pY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

/-- `map_split_keys_and_domains/1` on a single atom requires it. -/
theorem split_one (s : String) (m : Nat) :
    Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (atomT s) =
      .ok (.tuple #[Term.list [.atom s], .nil, .atom "nil", .nil, .nil]) := by
  rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
  simp [atomT, getMapKeys_single, mapLookup, Erlang.sets.«to_list/1», Erlang.maps.«keys/1», Term.list,
    Elixir.Module.Types.Descr.«to_domain_keys/1», Erlang.maps.«fold/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-to_domain_keys/1-fun-0-/3».pure,
    Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2»]

theorem descrC_map {Fn TF LF MF : Term → Prop} {r : Term} (mr : MF r) : DescrC Fn TF LF MF [(.atom "map", r)] where
  keys q h := by
    by_cases e : compareExact (fuel q (.atom "map")) q (.atom "map") = .eq
    · exact ⟨"map", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [mapLookup, e] at h
  fields name x h := by
    by_cases e : name = "map"
    · subst e
      simp [mapLookup] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mr⟩))))
    · simp [mapLookup, e] at h

section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` forcing a constant field at a key of static types of the next level: types holding only
maps, some of them, give the maps the field accepts that agree with one of their maps at the other keys; others give
`:badmap`. -/
theorem update_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v ov : Term}
    {P : MW (level t n).V → Prop} (lp : LeafPut (level t n).E (level t n).den a v ov P) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, ov]], .atom "force"]) (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.map [], .map Y, .nil] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ P w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨Y, rfl, ⟨w₀, hw₀⟩, r, fr, hY, sr⟩⟩ :=
        put_update_static (level t n).ef (n := k) (by omega) a lp hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
          P w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
        rw [sr]
        exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
      rcases hY with rfl | ⟨rfl, emp⟩
      · refine ⟨_, ?_, Or.inr ⟨_, rfl, only.mpr ⟨restE, w₀, hw₀⟩, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_,
          fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          by_cases e : q.1.1 = "map"
          · exact e
          · simp [mapLookup, e, dn_none] at hq
        · rw [← sem]; simp [MT, mapLookup]
      · refine ⟨_, ?_, Or.inr ⟨_, rfl, only.mpr ⟨restE, w₀, hw₀⟩, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_,
          fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          simp [mapLookup, dn_none] at hq
        · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]


/-- `map_put_key/3` on static types of the next level and a static value: types holding only maps, some of them, give
the maps whose key holds a value of the type and that agree with one of their maps at the other keys; others give
`:badmap`. -/
theorem put_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_put_key/3» (D m) (.map X) (.atom a) v = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.atom "ok", .map Y] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  have shared : Elixir.Module.Types.Descr.«map_put_key/3» (D m) (.map X) (.atom a) v =
      (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
          (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "false")
        match r with
        | .tuple ⟨[_, d, _]⟩ => pure (.tuple #[.atom "ok", d])
        | .tuple ⟨[.atom "error", _]⟩ => pure (.tuple #[.atom "ok", .map []])
        | .atom "badmap" => pure (.atom "badmap")
        | x => .error (.error (.tuple #[.atom "case_clause", x]))) := by
    unfold Elixir.Module.Types.Descr.«map_put_key/3» Elixir.Module.Types.Descr.«map_put_shared/3»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · simp [Term.list]
      rfl
    · simp [getMapKeys_single, sZ, Term.list]
      rfl
  obtain ⟨res, run, ⟨rfl, h⟩ | ⟨Y, rfl, h⟩⟩ := update_map hX a (leafPut_put (level t n).ef a hv) hm
  · exact ⟨_, by rw [shared, run]; rfl, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨_, by rw [shared, run]; rfl, Or.inr ⟨Y, rfl, h⟩⟩

/-- `map_update/5` deleting a single atom key of static types of the next level: types holding only maps, some of
them, give the maps without the key that agree with one of their maps at the other keys; others give `:badmap`. -/
theorem del_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) (.atom "delete") (.atom "force")
        (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ Y, res = .tuple #[.map [], .map Y, .nil] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ w (.atom a) = none ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := update_map hX a (leafPut_del (level t n).ef a) hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem force_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (bdd : Term) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ T Y, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, .nil, .atom "true"]) ∧ E T ∧
      (∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x)) ∧ PutMaps E den a (PutAt den v a) lines Y := by
  obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a lines hl
  obtain ⟨bdds, rb, fb, sb⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
  have rb : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
      .ok (.tuple #[Term.list bdds, F]) := by simpa [boolAtom] using rb Bool.true F (fun _ => rF)
  obtain ⟨ty, o, rfl, hty⟩ := hF
  obtain ⟨T, hT, rT, sT⟩ := ef.opt_union [] (m := n + 3) hty ef.none (by omega)
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[.map [], .nil, .nil, .atom "false"])
      (Term.list lines) (.cons (.atom a) .nil) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
      (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
      .ok (.tuple #[T, Term.list bdds, .nil, .atom "true"]) := by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb, Elixir.Module.Types.Descr.«opt_union/2», rT]
    rw [show (Term.nil) = Term.list [] from rfl, append_list]
    simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"])
      (.atom "false") (.atom "true") (.atom "true") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
    Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list, Term.properList?, nk₁,
    nk₂, Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
    Erlang.lists.«map/2»]
  have semT : ∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x) := by
    intro x
    rw [sT, ← sF, fieldSem_mk]
    have nx : ¬den (.map []) x := fun h => (none_field (den := den) ef).2 (some x)
      (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
    simp [nx]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have sem : ∀ w, denMF E den r w = Bool.true ↔ PutAt den v a w ∧ ∃ L ∈ lines, ∃ o, InMLine den L (setK a o w) :=
    fun w => (sr w).trans (sb w)
  by_cases bot : r = .atom "bdd_bot"
  · subst bot
    exact ⟨T, .map [], by simp [rr], hT, semT, .atom "bdd_bot", fr, Or.inr ⟨rfl, fun w => denMF_bot w⟩, sem⟩
  · refine ⟨T, .map [(.atom "map", r)], ?_, hT, semT, r, fr, Or.inl rfl, sem⟩
    simp only [rr, Lynx.Except.ok_bind]

/-- `map_update_static/5` forces a constant into a map field and returns the old values: `:badmap` when it is empty. -/
theorem force_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ (∃ w, denMF E den b w = Bool.true) ∧ E T ∧
          (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = some x) ∧
          PutField E den a (PutAt den v a) b Y) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨T, Y, rY, hT, sT, pY⟩ := force_static_dnf ef hn a hv (.tuple #[.integer k, tag, fieldsTerm l]) _ hl
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      refine ⟨_, ?_, Or.inr ⟨T, Y, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, hT, fun x => ?_, putMaps_field inB pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · rw [sT]
        exact ⟨fun ⟨L, mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L, mL, hw⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => by obtain ⟨L, mL, hL⟩ := (inB w).mp hw; exact ⟨L, mL, w, hL, wa⟩⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨T, Y, rY, hT, sT, pY⟩ := force_static_dnf ef hn a hv b (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, hT, fun x => ?_,
        putMaps_field inB pY⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · rw [sT]
        exact ⟨fun ⟨L', mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L', mL, hw⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => by obtain ⟨L', mL, hL⟩ := (inB w).mp hw; exact ⟨L', mL, w, hL, wa⟩⟩

section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` forcing a value at a key of static types of the next level and returning the old values:
types holding only maps, some of them, give the values of their maps at the key and the maps whose key holds a value of
the type that agree with one of their maps at the other keys; others give `:badmap`. -/
theorem force_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], .atom "force"]) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ MOnly t n X ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, Y, rfl, ⟨w₀, hw₀⟩, hT, sT, r, fr, hY, sr⟩⟩ :=
        force_update_static (level t n).ef (n := k) (by omega) a hv hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have semT : ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x := fun x => by
        rw [sT]; exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩⟩
      have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
          PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
        rw [sr]
        exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
      rcases hY with rfl | ⟨rfl, emp⟩
      · refine ⟨_, ?_, Or.inr ⟨T, _, rfl, only.mpr ⟨restE, w₀, hw₀⟩, hT, semT, Or.inr ⟨_, rfl, descrC_map fr⟩,
          fun q hq => ?_, fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          by_cases e : q.1.1 = "map"
          · exact e
          · simp [mapLookup, e, dn_none] at hq
        · rw [← sem]; simp [MT, mapLookup]
      · refine ⟨_, ?_, Or.inr ⟨T, _, rfl, only.mpr ⟨restE, w₀, hw₀⟩, hT, semT, Or.inr ⟨_, rfl, descrC_nil⟩,
          fun q hq => ?_, fun w => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
        · rw [denD_map] at hq
          simp [mapLookup, dn_none] at hq
        · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

/-- `map_update/5` forcing a static value at a single atom key, returning the old values. -/
theorem update_force {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) v (.atom "force") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ MOnly t n X ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := force_map hX a hv hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]

end

/-- `map_split_key_line/5` on a non-empty line: the field of the key, the rest of the literal without the key, the
negated literals split at the key, and the accumulated field united with the values at the key of the line's maps. -/
theorem split_line (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {tag : Term}
    {l : List (Term × Term)} {negs : List Term} (g : TagV E tag) (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      FieldValue E (fieldAt tag l a) ∧ MField E (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) ∧
      (∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
        MSem den tag (eraseKey a l) w) ∧
      (∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) ∧
      ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w) := by
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, hn₀⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, -⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  by_cases nn : negs = []
  · subst nn
    obtain ⟨t₁, o₁, e₁, h₁⟩ := hf
    obtain ⟨t₂, o₂, e₂, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) e₁ e₂ h₁ h₂ []
    refine ⟨k, [], .tuple #[c, boolAtom (o₁ || o₂)], ?_, ⟨c, _, rfl, hc⟩, fun o => ?_, ⟨t₁, o₁, e₁, h₁⟩, hb, rest,
      by simp, fun w => by simp⟩
    · simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run, rc, Term.list]
    · rw [sc, or_comm]
      refine or_congr Iff.rfl ⟨fun ho => long_of_rest ef a g (P := []) (by simp) (fun w => by simp) ho split₀.2
        (by simp), ?_⟩
      rintro ⟨w, hw, rfl⟩
      exact ((msem_at ef g l a w).mp (inMLine_iff.mp hw).1).1
  obtain ⟨N₀, negs₀, rfl⟩ : ∃ N₀ negs₀, negs = N₀ :: negs₀ := by
    cases negs with
    | nil => exact absurd rfl nn
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a (N₀ :: negs₀) lits []
  · exact absurd (hN w₀) (hn₀ N mN)
  simp only [List.append_nil] at rr
  have rr' := rr; simp only [Term.list] at rr'
  have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr split₀.2⟩
  obtain ⟨s, acc', rk, hs₁, hs₂, hacc, sacc⟩ := mproj_value ef hn P (fun p mp => (hP p mp).1) hf hb restNe ha
  refine ⟨k, P, acc', ?_, hacc, fun o => ?_, hf, hb, rest, hP, sP⟩
  · cases s
    · obtain ⟨Q, rQ, rf⟩ := hs₂ rfl
      cases P with
      | nil => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, rQ, rf, Lynx.Term.isMember, boolAtom,
          Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, rQ, rf, Lynx.Term.isMember, boolAtom,
          Term.list]
    · cases P with
      | nil => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, hs₁ rfl, Lynx.Term.isMember, boolAtom,
          Term.list]
      | cons p P => simp [Elixir.Module.Types.Descr.«map_split_key_line/5», run,
          Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr', rk, hs₁ rfl, Lynx.Term.isMember, boolAtom,
          Term.list]
  · rw [sacc]
    refine or_congr Iff.rfl ⟨fun ⟨w', hf', hr', out⟩ => long_of_rest ef a g hP sP hf' ((rest w').mp hr') out, ?_⟩
    rintro ⟨w, hw, rfl⟩
    obtain ⟨hmw, hnw⟩ := inMLine_iff.mp hw
    obtain ⟨hfw, hrw⟩ := (msem_at ef g l a w).mp hmw
    exact ⟨eraseK a w, hfw, (rest _).mpr hrw, fun p mp hp => by
      obtain ⟨N, mN, hN⟩ := (sP w).mpr ⟨p, mp, hp⟩
      exact hnw N mN hN⟩

/-- The field of an absent key. -/
def absF : Term := .tuple #[.map [], .atom "true"]

/-- Maps of rests paired with a field. -/
def WithF (E : Term → Prop) (den : Term → V → Prop) (f : Term) (Q : List Term) (u : MW V) : Prop :=
  ∃ b, Term.tuple #[f, b] ∈ Q ∧ denMF E den b u = Bool.true

/-- Pairs of a new field or the absent field, whose rests have literals without a key. -/
def UpdQ (E : Term → Prop) (a : String) (new : Term) (keep : Bool) (Q : List Term) : Prop :=
  ∀ q ∈ Q, ∃ f b, q = .tuple #[f, b] ∧ (f = new ∨ (keep = Bool.true ∧ f = absF)) ∧ MField E b ∧ OField (LitA E a) b

theorem withF_cons {f g b : Term} {Q : List Term} {u : MW V} :
    WithF E den f (.tuple #[g, b] :: Q) u ↔ (f = g ∧ denMF E den b u = Bool.true) ∨ WithF E den f Q u := by
  constructor
  · rintro ⟨b', mb, hb⟩
    rcases List.mem_cons.mp mb with e | mb
    · obtain ⟨rfl, rfl⟩ : f = g ∧ b' = b := by simpa using e
      exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr ⟨b', mb, hb⟩
  · rintro (⟨rfl, hb⟩ | ⟨b', mb, hb⟩)
    · exact ⟨b, List.mem_cons_self, hb⟩
    · exact ⟨b', List.mem_cons_of_mem _ mb, hb⟩

theorem withF_nil {f : Term} {u : MW V} : ¬WithF E den f [] u := fun ⟨_, m, _⟩ => by simp at m

theorem new_ne_absF {v : Term} : Term.tuple #[v, .atom "false"] ≠ absF := by
  intro h; simp [absF] at h

theorem withF_append {f : Term} {A B : List Term} {u : MW V} :
    WithF E den f (A ++ B) u ↔ WithF E den f A u ∨ WithF E den f B u := by
  constructor
  · rintro ⟨b, mb, hb⟩
    rcases List.mem_append.mp mb with mb | mb
    · exact Or.inl ⟨b, mb, hb⟩
    · exact Or.inr ⟨b, mb, hb⟩
  · rintro (⟨b, mb, hb⟩ | ⟨b, mb, hb⟩)
    · exact ⟨b, List.mem_append_left _ mb, hb⟩
    · exact ⟨b, List.mem_append_right _ mb, hb⟩

theorem withF_single {f g b : Term} {u : MW V} :
    WithF E den f [.tuple #[g, b]] u ↔ f = g ∧ denMF E den b u = Bool.true := by
  rw [withF_cons]; simp [withF_nil]

theorem mInPairs_append {A B : List Term} {y : Option V} {u : MW V} :
    MInPairs E den (A ++ B) y u ↔ MInPairs E den A y u ∨ MInPairs E den B y u := by
  simp only [MInPairs, List.mem_append]
  constructor
  · rintro ⟨p, mp | mp, hp⟩
    · exact Or.inl ⟨p, mp, hp⟩
    · exact Or.inr ⟨p, mp, hp⟩
  · rintro (⟨p, mp, hp⟩ | ⟨p, mp, hp⟩)
    · exact ⟨p, Or.inl mp, hp⟩
    · exact ⟨p, Or.inr mp, hp⟩

/-- The final fold of `map_update_project_pair/5`: pairs whose old type has values give the new field with their rest,
optional ones the absent field. -/
theorem upd_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a : String) {v : Term} (keep : Bool)
    (Q' : List Term) (hQ : MQOk E den Q') (kQ : KeepsQ (LitA E a) Q')
    (opt : ∀ q ∈ Q', ∀ t b, q = .tuple #[.tuple #[t, .atom "true"], b] → keep = Bool.true)
    (acc : List Term) (ha : UpdQ E a (.tuple #[v, .atom "false"]) keep acc) :
    ∃ Qf, Erlang.lists.«foldl/3» (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_project_pair/5-fun-0-" 2 #[.tuple #[v, .atom "false"]])
        (Term.list acc) (Term.list Q') = .ok (Term.list Qf) ∧ UpdQ E a (.tuple #[v, .atom "false"]) keep Qf ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Qf u ↔
        WithF E den (.tuple #[v, .atom "false"]) acc u ∨ ∃ x, MInPairs E den Q' (some x) u) ∧
      (∀ u, WithF E den absF Qf u ↔ WithF E den absF acc u ∨ MInPairs E den Q' none u) := by
  obtain ⟨r, ⟨Qf, rfl, uQ, sN, sA⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_project_pair/5-fun-0-" #[.tuple #[v, .atom "false"]]
    (fun pre r => ∃ Qf, r = Term.list Qf ∧ UpdQ E a (.tuple #[v, .atom "false"]) keep Qf ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Qf u ↔
        WithF E den (.tuple #[v, .atom "false"]) acc u ∨ ∃ x, MInPairs E den pre (some x) u) ∧
      (∀ u, WithF E den absF Qf u ↔ WithF E den absF acc u ∨ MInPairs E den pre none u)) Q'
    (fun pre q r mq ⟨Qf, er, uQ, sN, sA⟩ => by
      subst er
      obtain ⟨f, b, rfl, ⟨t, o, rfl, ht⟩, fb, nb⟩ := hQ q mq
      obtain ⟨f', b', e', ob⟩ := kQ _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
      obtain ⟨-, rfl⟩ := e'
      obtain ⟨eb, re, se⟩ := ef.empty1 (m := n) hn ht
      let Q₁ := (if o then [Term.tuple #[absF, b]] else []) ++
        ((if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) ++ Qf)
      have keepO : o = Bool.true → keep = Bool.true := fun h => opt _ mq t b (by subst h; rfl)
      refine ⟨Term.list Q₁, ⟨Q₁, rfl, fun q' mq' => ?_, fun u => ?_, fun u => ?_⟩, ?_⟩
      · simp only [Q₁, List.mem_append] at mq'
        rcases mq' with mq' | mq' | mq'
        · cases o
          · simp at mq'
          · simp at mq'; subst mq'; exact ⟨absF, b, rfl, Or.inr ⟨keepO rfl, rfl⟩, fb, ob⟩
        · cases eb
          · simp at mq'; subst mq'; exact ⟨_, b, rfl, Or.inl rfl, fb, ob⟩
          · simp at mq'
        · exact uQ q' mq'
      · have pin : ∀ x, MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] (some x) u ↔
            den t x ∧ denMF E den b u = Bool.true := fun x => by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : WithF E den (.tuple #[v, .atom "false"])
            (if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) u ↔
            ∃ x, den t x ∧ denMF E den b u = Bool.true := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]
            obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
              have := se.mpr fun v hv => h ⟨v, hv⟩
              cases this
            exact ⟨fun ⟨_, h⟩ => ⟨x, hx, h⟩, fun ⟨_, _, h⟩ => ⟨trivial, h⟩⟩
          · simp only [↓reduceIte]
            exact ⟨fun h => absurd h withF_nil, fun ⟨x, hx, _⟩ => absurd hx (se.mp rfl x)⟩
        have first : ¬WithF E den (.tuple #[v, .atom "false"]) (if o then [Term.tuple #[absF, b]] else []) u := by
          cases o
          · exact withF_nil
          · simp only [↓reduceIte, withF_single]; exact fun ⟨h, _⟩ => new_ne_absF h
        simp only [Q₁, withF_append, sN, mInPairs_append, pin]
        constructor
        · rintro (h | h | h | h)
          · exact absurd h first
          · exact Or.inr ⟨_, Or.inr ((mid.mp h).choose_spec)⟩
          · exact Or.inl h
          · obtain ⟨x, hx⟩ := h; exact Or.inr ⟨x, Or.inl hx⟩
        · rintro (h | ⟨x, h | h⟩)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr ⟨x, h⟩))
          · exact Or.inr (Or.inl (mid.mpr ⟨x, h⟩))
      · have pin : MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] none u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : ¬WithF E den absF (if eb then [] else [Term.tuple #[.tuple #[v, .atom "false"], b]]) u := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]; exact fun ⟨h, _⟩ => new_ne_absF h.symm
          · exact withF_nil
        have first : WithF E den absF (if o then [Term.tuple #[absF, b]] else []) u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          cases o
          · simp [withF_nil]
          · simp only [↓reduceIte, withF_single]
        simp only [Q₁, withF_append, sA, mInPairs_append, pin, first]
        constructor
        · rintro (h | h | h | h)
          · exact Or.inr (Or.inr h)
          · exact absurd h mid
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_project_pair/5-fun-0-/2».pure]
        cases o <;> cases eb <;>
          simp [Elixir.Module.Types.Descr.«-map_update_project_pair/5-fun-0-/3», re, Lynx.Term.isMember, boolAtom, Q₁, absF,
            Term.list])
    (Term.list acc) ⟨acc, rfl, ha, fun u => by simp [MInPairs], fun u => by simp [MInPairs]⟩
  exact ⟨Qf, run, uQ, sN, sA⟩

/-- `map_update_project_pair/5` updates the maps of a pair minus negated pairs whose key holds a value, and with
`keep_absent?`, keeps those without the key. -/
theorem project5 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (P : List Term)
    (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) {t : Term} {o : Bool} {rest : Term} (ht : E t)
    (hr : MField E rest) (orest : OField (LitA E a) rest) (nr : ∃ w, denMF E den rest w = Bool.true)
    {v : Term} (hv : E v) (vne : ∃ x, den v x) (keep : Bool) :
    ∃ Q, Elixir.Module.Types.Descr.«map_update_project_pair/5» (D (n + 2)) (Term.list P) (.tuple #[t, boolAtom o]) rest
        (.tuple #[v, .atom "false"]) (boolAtom keep) = .ok (Term.list Q) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep Q ∧
      (∀ u, WithF E den (.tuple #[v, .atom "false"]) Q u ↔
        ∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∧
      (∀ u, WithF E den absF Q u ↔
        keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  obtain ⟨b₀, rb₀, sb₀⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (putFieldV hv)
  have b₀f : b₀ = Bool.false := by
    cases b₀
    · rfl
    · obtain ⟨x, hx⟩ := vne
      exact absurd ((putField_sem (some x)).mpr ⟨x, rfl, hx⟩) (sb₀.mp rfl (some x))
  subst b₀f
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 2) (by omega) ht
  obtain ⟨s₁, rs₁, ss₁⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' (field := .tuple #[t, .atom "false"])
    ⟨t, Bool.false, rfl, ht⟩
  have hA : FieldValue E absF := ⟨.map [], Bool.true, rfl, ef.none⟩
  obtain ⟨s₂, rs₂, ss₂⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hA
  -- The shortcuts: the full rest with the new field, and with the absent field.
  let s₁₇ := !e && s₁
  let s₂₇ := keep && o && s₂
  let t₂ := if s₁₇ then Term.map [] else t
  let o₂ := if s₂₇ then Bool.false else (keep && o)
  let pairs₁ := (if s₂₇ then [Term.tuple #[absF, rest]] else []) ++
    (if s₁₇ then [Term.tuple #[.tuple #[v, .atom "false"], rest]] else [])
  have ht₂ : E t₂ := by simp only [t₂]; split; exact ef.none; exact ht
  obtain ⟨fe, rfe, sfe⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (⟨t₂, o₂, rfl, ht₂⟩ : FieldValue E _)
  obtain ⟨Q', rQ', qQ', kQ', fQ', sQ'⟩ := mproject_pairs ef hn P hP' ⟨t₂, o₂, rfl, ht₂⟩ hr nr
  have up₁ : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs₁ := by
    intro q mq
    simp only [pairs₁, List.mem_append] at mq
    rcases mq with mq | mq
    · by_cases h : s₂₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        refine ⟨absF, rest, rfl, Or.inr ⟨?_, rfl⟩, hr, orest⟩
        simp only [s₂₇, Bool.and_eq_true] at h; exact h.1.1
      · rw [ite_eq_right h] at mq; simp at mq
    · by_cases h : s₁₇
      · rw [ite_eq_left h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨_, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [ite_eq_right h] at mq; simp at mq
  have opt : ∀ q ∈ Q', ∀ t' b, q = .tuple #[.tuple #[t', .atom "true"], b] → keep = Bool.true := by
    intro q mq t' b eq
    obtain ⟨f, b', e', -, -, w, hw⟩ := qQ' q mq
    subst eq
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
    obtain ⟨rfl, rfl⟩ := e'
    have := ((sQ' none w).mp ⟨_, mq, mpairIn_iff.mpr ⟨by
      rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; exact Or.inl ⟨rfl, rfl⟩, hw⟩⟩).1
    rw [fieldSem_mk] at this
    rcases this with ⟨-, h⟩ | ⟨x, h, -⟩
    · simp only [o₂] at h; split at h
      · cases h
      · simp only [Bool.and_eq_true] at h; exact h.1
    · cases h
  obtain ⟨Qf, rQf, uQf, sNf, sAf⟩ := upd_fold ef (n := n + 1) (by omega) a keep Q' qQ' (kQ' _ orest kP) opt pairs₁ up₁
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  have pres₁ : ∀ u, WithF E den (.tuple #[v, .atom "false"]) pairs₁ u ↔ s₁₇ = Bool.true ∧
      denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    have h₁ : ¬WithF E den (.tuple #[v, .atom "false"]) (if s₂₇ then [Term.tuple #[absF, rest]] else []) u := by
      by_cases h : s₂₇
      · simp only [h, ↓reduceIte, withF_single]; exact fun ⟨e, _⟩ => new_ne_absF e
      · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact withF_nil
    by_cases h : s₁₇
    · simp only [h, ↓reduceIte, withF_single, true_and]; exact ⟨fun h' => h'.elim (absurd · h₁) id, Or.inr⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
      exact fun h' => h'.elim h₁ withF_nil
  have abs₁ : ∀ u, WithF E den absF pairs₁ u ↔ s₂₇ = Bool.true ∧ denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    have h₂ : ¬WithF E den absF (if s₁₇ then [Term.tuple #[.tuple #[v, .atom "false"], rest]] else []) u := by
      by_cases h : s₁₇
      · simp only [h, ↓reduceIte, withF_single]; exact fun ⟨e, _⟩ => new_ne_absF e.symm
      · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact withF_nil
    by_cases h : s₂₇
    · simp only [h, ↓reduceIte, withF_single, true_and]; exact ⟨fun h' => h'.elim id (absurd · h₂), Or.inl⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
      try exact fun h' => h'.elim withF_nil h₂
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
  -- The witness of the first shortcut: a value of the old type outside every negated pair.
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
  refine ⟨if fe then pairs₁ else Qf, ?_, ?_, ?_, ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_project_pair/5»
    have rs₁ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        (.tuple #[t, .atom "false"]) = .ok (boolAtom s₁) := rs₁
    have rs₂ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        absF = .ok (boolAtom s₂) := rs₂
    simp only [s₁₇, s₂₇, t₂, o₂, pairs₁, absF] at rfe rQ' rQf rs₂
    clear ss₁ ss₂ sQ' sNf sAf se sfe sb₀ uQf up₁ opt qQ' kQ' fQ' hP hP' kP
    cases fe <;> cases e <;> cases s₁ <;> cases keep <;> cases o <;> cases s₂ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, boolAtom, s₁₇, s₂₇, pairs₁,
        List.cons_append, Term.list] at rfe rQ' rQf rs₁ rs₂ ⊢ <;>
      simp [rb₀, re, rs₁, rs₂, rfe, rQ', rQf, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, absF]
  · cases fe
    · exact uQf
    · exact up₁
  · intro u
    cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sNf, pres₁]
      constructor
      · rintro (⟨h, hr⟩ | ⟨x, hx⟩)
        · obtain ⟨x, hx, out⟩ := short₁ h
          exact ⟨x, hx, hr, fun p mp => out u p mp⟩
        · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
          obtain ⟨x', e, -, hx'⟩ | ⟨e, -⟩ := (f₂ _).mp hf
          · obtain rfl : x = x' := Option.some.inj e
            exact ⟨x, hx', hr, out⟩
          · cases e
      · rintro ⟨x, hx, hr, out⟩
        by_cases h : s₁₇
        · exact Or.inl ⟨h, hr⟩
        · exact Or.inr ⟨x, (sQ' _ u).mpr ⟨(f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩), hr, out⟩⟩
    · simp only [↓reduceIte]
      rw [pres₁]
      constructor
      · rintro ⟨h, hr⟩
        obtain ⟨x, hx, out⟩ := short₁ h
        exact ⟨x, hx, hr, fun p mp => out u p mp⟩
      · rintro ⟨x, hx, hr, out⟩
        by_cases h : s₁₇
        · exact ⟨h, hr⟩
        · exact absurd ((f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩)) (sfe.mp rfl (some x))
  · intro u
    have o₂e : o₂ = Bool.true ↔ s₂₇ = Bool.false ∧ keep = Bool.true ∧ o = Bool.true := by
      simp only [o₂]
      by_cases h : s₂₇
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, true_and]; try simpa using h
    cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sAf, abs₁]
      constructor
      · rintro (⟨h, hr⟩ | hx)
        · obtain ⟨hk, ho, out⟩ := short₂ h
          exact ⟨hk, ho, hr, fun p mp => out u p mp⟩
        · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
          obtain ⟨x, e, -⟩ | ⟨-, h⟩ := (f₂ _).mp hf
          · cases e
          · obtain ⟨-, hk, ho⟩ := o₂e.mp h
            exact ⟨hk, ho, hr, out⟩
      · rintro ⟨hk, ho, hr, out⟩
        by_cases h : s₂₇
        · exact Or.inl ⟨h, hr⟩
        · exact Or.inr ((sQ' _ u).mpr ⟨(f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩), hr, out⟩)
    · simp only [↓reduceIte]
      rw [abs₁]
      constructor
      · rintro ⟨h, hr⟩
        obtain ⟨hk, ho, out⟩ := short₂ h
        exact ⟨hk, ho, hr, fun p mp => out u p mp⟩
      · rintro ⟨hk, ho, hr, out⟩
        by_cases h : s₂₇
        · exact ⟨h, hr⟩
        · exact absurd ((f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩)) (sfe.mp rfl none)

theorem tuple2_exact {a₀ a₁ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁]) b) (.tuple #[a₀, a₁]) b = .eq) :
    ∃ b₀ b₁, b = .tuple #[b₀, b₁] ∧ compareExact (fuel a₀ b₀) a₀ b₀ = .eq ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, rfl, e.1, e.2⟩

/-- The new field and the absent field are distinct keys. -/
theorem new_absF_apart (v : Term) :
    compareExact (fuel (.tuple #[v, .atom "false"]) absF) (.tuple #[v, .atom "false"]) absF ≠ .eq := by
  intro e
  obtain ⟨b₀, b₁, eb, -, e₁⟩ := tuple2_exact e
  simp only [absF, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eb
  obtain ⟨-, rfl⟩ := eb
  simp at e₁

theorem absF_new_apart (v : Term) :
    compareExact (fuel absF (.tuple #[v, .atom "false"])) absF (.tuple #[v, .atom "false"]) ≠ .eq := by
  intro e
  obtain ⟨b₀, b₁, eb, -, e₁⟩ := tuple2_exact e
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eb
  obtain ⟨-, rfl⟩ := eb
  simp at e₁

/-- Uniting rests without a key and putting a field there: the maps the field accepts whose other keys are those of
one of the rests. -/
theorem put_rests (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v ov : Term} {P : MW V → Prop}
    (lp : LeafPut E den a v ov P) (rs : List Term) (hrs : ∀ b ∈ rs, MField E b ∧ OField (LitA E a) b) :
    ∃ r', (do
        let u ← Elixir.Module.Types.Descr.«map_union_all/1» (D m) (Term.list rs)
        Elixir.Module.Types.Descr.«map_put_key_bdd/5» u (.atom a) v ov (.atom "false")) = .ok r' ∧ MField E r' ∧
      ∀ w, denMF E den r' w = Bool.true ↔ P w ∧ ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := by
  obtain ⟨r, rr, -, kr, sr⟩ := munion_all (den := den) ef hm (mergeOk_litA a) _ rs (Nat.le_refl _) hrs
  rcases kr with ⟨k, rfl⟩ | wr
  · obtain ⟨lit', run, ml', il', sem⟩ := lp.top k
    obtain ⟨k', x, y, rfl⟩ := il'
    refine ⟨_, ?_, Or.inr (Bdd.leaf_iff.mpr ml'), fun w => ?_⟩
    · simp [rr, Elixir.Module.Types.Descr.«map_put_key_bdd/5», run]
    · have top := (sr (eraseK a w)).mp (by simp [denMF_top])
      rw [denMF_bdd (Bdd.leaf_iff.mpr ml'), eval_leaf, sem, bp_true]
      exact ⟨fun h => ⟨h, top⟩, fun h => h.1⟩
  obtain ⟨r', run, wr', sem⟩ := put_bdd a lp _ r wr (fun _ h => h) Bool.false
  have wr₀ : Bdd (MLit E) r := wr.mono fun _ h => h.1
  refine ⟨r', ?_, Or.inr wr', fun w => ?_⟩
  · simpa [rr] using run
  · rw [denMF_bdd wr', ← sr, denMF_bdd wr₀]
    by_cases hp : P w
    · rw [(sem w).1 hp]; simp [hp]
    · rw [(sem w).2 rfl hp]; simp [hp]

/-- The fields of updates: the new field or the absent one. -/
def UKey (v f : Term) : Prop := f = .tuple #[v, .atom "false"] ∨ f = absF

theorem keyed_apart {v f g : Term} (hf : UKey v f) (hg : UKey v g) (ne : f ≠ g) :
    compareExact (fuel g f) g f ≠ .eq := by
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact absurd rfl ne
  · exact absF_new_apart v
  · exact new_absF_apart v
  · exact absurd rfl ne

theorem lookup_same {f val : Term} {es : List (Term × Term)} : mapLookup ((f, val) :: es) f = some val := by
  simp [mapLookup]

theorem lookup_other {v f g val : Term} {es : List (Term × Term)} (hf : UKey v f) (hg : UKey v g) (ne : f ≠ g) :
    mapLookup ((f, val) :: es) g = mapLookup es g := by
  simp [mapLookup, keyed_apart hf hg ne]

/-- Groups of rests by field: every binding names a field of updates and rests of pairs with that field, and every
pair is found by its field. -/
def GInv (v : Term) (pre : List Term) (entries : List (Term × Term)) : Prop :=
  (∀ e ∈ entries, UKey v e.1 ∧ ∃ rs, e.2 = Term.list rs ∧ ∀ b ∈ rs, Term.tuple #[e.1, b] ∈ pre) ∧
  ∀ f b, Term.tuple #[f, b] ∈ pre → ∃ rs, mapLookup entries f = some (Term.list rs) ∧ b ∈ rs

/-- The grouping fold of `map_update_named_key/5`. -/
theorem group_fold {v : Term} (m : Nat) (pairs : List Term)
    (hp : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey v f) :
    ∃ entries, Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[])
        (.map []) (Term.list pairs) = .ok (.map entries) ∧ GInv v pairs entries := by
  obtain ⟨r, ⟨-, entries, rfl, inv⟩, run⟩ := foldl_rel_at (m := m) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-1-" #[]
    (fun pre r => (∀ q ∈ pre, ∃ f b, q = .tuple #[f, b] ∧ UKey v f) ∧ ∃ entries, r = .map entries ∧ GInv v pre entries)
    pairs
    (fun pre q r mq ⟨kp, entries, er, ⟨h₁, h₂⟩⟩ => by
      subst er
      obtain ⟨f, b, rfl, kf⟩ := hp q mq
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-1-/2».pure]
      -- The rests already grouped under the field, if any.
      obtain ⟨rs, hl, hrs⟩ : ∃ rs : List Term, (mapLookup entries f = some (Term.list rs) ∨
          (mapLookup entries f = none ∧ rs = [])) ∧ ∀ b' ∈ rs, Term.tuple #[f, b'] ∈ pre := by
        cases hlk : mapLookup entries f with
        | none => exact ⟨[], Or.inr ⟨rfl, rfl⟩, by simp⟩
        | some val =>
          obtain ⟨e, me, ee, rfl⟩ : ∃ e ∈ entries, compareExact (fuel f e.1) f e.1 = .eq ∧ e.2 = val := by
            simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hlk
            obtain ⟨e, he, rfl⟩ := hlk
            exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩
          obtain ⟨ke, rs, hv, hb⟩ := h₁ e me
          have : e.1 = f := Classical.byContradiction fun ne => keyed_apart ke kf ne ee
          rw [this] at hb
          exact ⟨rs, Or.inl (by rw [hv]), hb⟩
      refine ⟨Term.map ((f, Term.list (b :: rs)) :: entries), ⟨fun q' mq' => ?_, _, rfl, fun e me => ?_,
        fun g b' mb => ?_⟩, ?_⟩
      · rcases List.mem_append.mp mq' with mq' | mq'
        · exact kp q' mq'
        · rw [List.mem_singleton] at mq'; exact ⟨f, b, mq', kf⟩
      · rcases List.mem_cons.mp me with rfl | me
        · refine ⟨kf, b :: rs, rfl, fun b'' mb'' => ?_⟩
          rcases List.mem_cons.mp mb'' with rfl | mb''
          · exact List.mem_append_right _ (List.mem_singleton_self _)
          · exact List.mem_append_left _ (hrs b'' mb'')
        · obtain ⟨ke, rs', hv, hb⟩ := h₁ e me
          exact ⟨ke, rs', hv, fun b'' mb'' => List.mem_append_left _ (hb b'' mb'')⟩
      · rcases List.mem_append.mp mb with mb | mb
        · obtain ⟨f', b'', e', kg⟩ := kp _ mb
          simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
          obtain ⟨rfl, rfl⟩ := e'
          obtain ⟨rs₀, hl₀, mb₀⟩ := h₂ g b' mb
          by_cases e : f = g
          · subst e
            rcases hl with hl | ⟨hl, -⟩
            · rw [hl₀] at hl
              have e₁ := congrArg Term.properList? (Option.some.inj hl)
              simp only [Term.properList?_list, Option.some.injEq] at e₁
              exact ⟨b :: rs, lookup_same, List.mem_cons_of_mem _ (e₁ ▸ mb₀)⟩
            · rw [hl₀] at hl; cases hl
          · exact ⟨rs₀, by rw [lookup_other kf kg e, hl₀], mb₀⟩
        · rw [List.mem_singleton] at mb
          simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at mb
          rw [mb.1, mb.2]
          exact ⟨b :: rs, lookup_same, List.mem_cons_self⟩
      · rcases hl with hl | ⟨hl, rfl⟩
        · have found : (entries.find? fun entry => decide (compareExact (fuel f entry.1) f entry.1 = .eq)).isSome := by
            simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hl
            obtain ⟨e, he, -⟩ := hl
            simp [he]
          simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-1-/2», getMapKeys_single, hl,
            Erlang.erlang.«is_map/1», Erlang.maps.«update/3», found, Term.list]
        · simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-1-/2», getMapKeys_single, hl,
            Erlang.maps.«put/3», Term.list])
    (.map []) ⟨by simp, [], rfl, by simp, by simp⟩
  exact ⟨entries, run, inv⟩

/-- The puts of `map_update_named_key/5` over groups of rests: the new field into the rests of present keys, and the
absent field into the rests of absent ones. -/
theorem group_bdds (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v : Term} (hv : E v)
    {keep : Bool} (pairs : List Term) (hp : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs)
    (entries : List (Term × Term)) (inv : GInv v pairs entries) :
    ∃ bdds, Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
        #[.atom a]) (Term.list ((mapEntries entries).map fun e => .tuple #[e.1, e.2])) = .ok (Term.list bdds) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w)) ∨
        (w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w)) := by
  classical
  have each : ∀ x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]), ∃ r,
      (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1 #[.atom a]) #[x] =
        .ok r ∧ MField E r ∧ ∃ e ∈ mapEntries entries, x = .tuple #[e.1, e.2] ∧ ∃ rs, e.2 = Term.list rs ∧
          ∀ w, denMF E den r w = Bool.true ↔
            ((e.1 = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (e.1 = absF ∧ w (.atom a) = none)) ∧
            ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨ke, rs, hv', hb⟩ := (inv.1 e (mem_of_mem_mapEntries me))
    have hrs : ∀ b ∈ rs, MField E b ∧ OField (LitA E a) b := fun b mb => by
      obtain ⟨f, b', eq, -, fb, ob⟩ := hp _ (hb b mb)
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eq
      obtain ⟨-, rfl⟩ := eq
      exact ⟨fb, ob⟩
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-2-/1».pure]
    rcases ke with ke | ke
    · obtain ⟨r, rr, fr, sr⟩ := put_rests ef hm a (leafPut_put ef a hv) rs hrs
      refine ⟨r, ?_, fr, e, me, rfl, rs, hv', fun w => ?_⟩
      · rw [ke, hv']; simpa [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-2-/2»] using rr
      · rw [sr]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨Or.inl ⟨ke, h₁⟩, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.elim (·.2) fun ⟨h, _⟩ =>
          absurd (ke.symm.trans h) new_ne_absF, h₂⟩⟩
    · obtain ⟨r, rr, fr, sr⟩ := put_rests ef hm a (leafPut_del ef a) rs hrs
      refine ⟨r, ?_, fr, e, me, rfl, rs, hv', fun w => ?_⟩
      · rw [ke, hv']; simpa [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-2-/2», absF] using rr
      · rw [sr]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨Or.inr ⟨ke, h₁⟩, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.elim (fun ⟨h, _⟩ =>
          absurd (h.symm.trans ke) new_ne_absF) (·.2), h₂⟩⟩
  let g : Term → Term := fun x => if hx : x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]) then
    Classical.choose (each x hx) else .nil
  have hg : ∀ x ∈ (mapEntries entries).map (fun e => Term.tuple #[e.1, e.2]),
      (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1 #[.atom a]) #[x] =
        .ok (g x) ∧ MField E (g x) ∧ ∃ e ∈ mapEntries entries, x = .tuple #[e.1, e.2] ∧ ∃ rs, e.2 = Term.list rs ∧
          ∀ w, denMF E den (g x) w = Bool.true ↔
            ((e.1 = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (e.1 = absF ∧ w (.atom a) = none)) ∧
            ∃ b ∈ rs, denMF E den b (eraseK a w) = Bool.true := fun x hx => by
    simp only [g, dite_eq_left hx]
    exact Classical.choose_spec (each x hx)
  refine ⟨((mapEntries entries).map fun e => Term.tuple #[e.1, e.2]).map g,
    map_list _ _ _ _ g _ fun x hx => (hg x hx).1, fun b mb => ?_, fun w => ?_⟩
  · obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mb
    exact (hg x mx).2.1
  -- The rests of a field, found among the enumerated bindings.
  have find : ∀ f b', UKey v f → Term.tuple #[f, b'] ∈ pairs → ∃ x ∈ (mapEntries entries).map
      (fun e => Term.tuple #[e.1, e.2]), ∃ rs, x = .tuple #[f, Term.list rs] ∧ b' ∈ rs := by
    intro f b' kf mb
    obtain ⟨rs, hl, mr⟩ := inv.2 f b' mb
    rw [← mapLookup_mapEntries] at hl
    simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hl
    obtain ⟨e, he, ee⟩ := hl
    have me := List.mem_of_find?_eq_some he
    have ce : compareExact (fuel f e.1) f e.1 = .eq := by simpa using List.find?_some he
    have : e.1 = f := Classical.byContradiction fun ne =>
      keyed_apart (inv.1 e (mem_of_mem_mapEntries me)).1 kf ne ce
    exact ⟨_, List.mem_map.mpr ⟨e, me, rfl⟩, rs, by rw [this, ee], mr⟩
  have unlist : ∀ {xs ys : List Term}, Term.list xs = Term.list ys → xs = ys := fun h => by
    have := congrArg Term.properList? h
    simpa [Term.properList?_list] using this
  constructor
  · rintro ⟨b, mb, hb⟩
    obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mb
    obtain ⟨-, -, e, me, rfl, rs, hrs, sem⟩ := hg x mx
    obtain ⟨⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩, b', mb', hb'⟩ := (sem w).mp hb
    all_goals
      obtain ⟨-, rs', hrs', inp⟩ := inv.1 e (mem_of_mem_mapEntries me)
      rw [hrs] at hrs'
      obtain rfl := unlist hrs'
    · exact Or.inl ⟨h₁', b', by rw [← h₁]; exact inp b' mb', hb'⟩
    · exact Or.inr ⟨h₁', b', by rw [← h₁]; exact inp b' mb', hb'⟩
  · have back : ∀ f b', UKey v f → Term.tuple #[f, b'] ∈ pairs → denMF E den b' (eraseK a w) = Bool.true →
        ((f = .tuple #[v, .atom "false"] ∧ PutAt den v a w) ∨ (f = absF ∧ w (.atom a) = none)) →
        ∃ b ∈ ((mapEntries entries).map fun e => Term.tuple #[e.1, e.2]).map g, denMF E den b w = Bool.true := by
      intro f b' kf mb' hb' hf
      obtain ⟨x, mx, rs, rfl, mr⟩ := find f b' kf mb'
      obtain ⟨-, -, e, me, ex, rs', hrs, sem⟩ := hg _ mx
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ex
      obtain ⟨e₁, e₂⟩ := ex
      rw [← e₂] at hrs
      obtain rfl := unlist hrs
      refine ⟨_, List.mem_map.mpr ⟨_, mx, rfl⟩, (sem w).mpr ⟨?_, b', mr, hb'⟩⟩
      rw [← e₁]; exact hf
    rintro (⟨hp', b', mb', hb'⟩ | ⟨hn, b', mb', hb'⟩)
    · exact back _ b' (Or.inl rfl) mb' hb' (Or.inl ⟨rfl, hp'⟩)
    · exact back _ b' (Or.inr rfl) mb' hb' (Or.inr ⟨rfl, hn⟩)


/-- The mode atom of `:keep` and `:reject`. -/
def modeT (keep : Bool) : Term := .atom (if keep then "keep" else "reject")

/-- One line of the general clause of `map_update_named_key/5` with a constant: the pairs of the line's maps whose
key holds a value, as maps with the key removed, and with `:keep`, of those without the key. -/
theorem line_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) {tag : Term} {l : List (Term × Term)} {negs : List Term} (g : TagV E tag)
    (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term) (Q : List Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      Elixir.Module.Types.Descr.«map_update_prepare_pairs/4» (D (n + 2)) (Term.list P) (fieldAt tag l a)
        (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) = .ok (Term.list Q) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep Q ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) Q (eraseK a w) ↔
        ∃ x, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a (some x) w)) ∧
      (∀ w, WithF E den absF Q (eraseK a w) ↔
        keep = Bool.true ∧ InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a none w)) := by
  obtain ⟨k, P, acc', run, hacc, sacc, hf, hb, rest, hP, sP⟩ := split_line ef hn a g sl lits ne ha
  obtain ⟨w₀, hw₀⟩ := ne
  have nr : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr ((msem_at ef g l a w₀).mp (inMLine_iff.mp hw₀).1).2⟩
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  obtain ⟨t, o, ef', ht⟩ := hf
  obtain ⟨Q, rQ, uQ, sN, sA⟩ := project5 ef hn a P hP ht hb orest nr hv vne keep
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
  refine ⟨k, P, acc', Q, run, ?_, hacc, sacc, uQ, fun w => ?_, fun w => ?_⟩
  · rw [ef']
    cases keep
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom] using rQ
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom] using rQ
  · rw [sN]
    refine ⟨fun ⟨x, hx, hr, out⟩ => ⟨x, (line w (some x)).mpr ⟨?_, hr, out⟩⟩, fun ⟨x, hx⟩ => ?_⟩
    · rw [fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩
    · obtain ⟨hf', hr, out⟩ := (line w (some x)).mp hx
      rw [fieldSem_mk] at hf'
      rcases hf' with ⟨h, -⟩ | ⟨x', e, hx'⟩
      · cases h
      · cases e; exact ⟨x, hx', hr, out⟩
  · rw [sA, line, fieldSem_mk]
    constructor
    · rintro ⟨hk, ho, hr, out⟩; exact ⟨hk, Or.inl ⟨rfl, ho⟩, hr, out⟩
    · rintro ⟨hk, ⟨-, ho⟩ | ⟨x, e, -⟩, hr, out⟩
      · exact ⟨hk, ho, hr, out⟩
      · cases e

/-- The line fold of the general clause of `map_update_named_key/5`. -/
theorem keep_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ (pr : List Term) (F : Term), Erlang.lists.«foldl/3» (D (n + 3))
        (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-0-" 2
          #[.atom a, .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]])
        (.tuple #[.nil, .tuple #[.map [], .atom "false"]]) (Term.list lines) = .ok (.tuple #[Term.list pr, F]) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep pr ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) ↔
        ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∧
      (∀ w, WithF E den absF pr (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) := by
  obtain ⟨r, ⟨pr, F, rfl, hF, sF, uQ, sN, sA⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-0-" #[.atom a, .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]]
    (fun pre r => ∃ (pr : List Term) (F : Term), r = .tuple #[Term.list pr, F] ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ pre, LongM den L a o) ∧
      UpdQ E a (.tuple #[v, .atom "false"]) keep pr ∧
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) ↔
        ∃ L ∈ pre, ∃ x, InMLine den L (setK a (some x) w)) ∧
      (∀ w, WithF E den absF pr (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ pre, InMLine den L (setK a none w))) lines
    (fun pre L r mL ⟨pr, F, er, hF, sF, uQ, sN, sA⟩ => by
      subst er
      obtain ⟨⟨tag, l, negs, rfl, g, sl, lits⟩, ne⟩ := hl L mL
      obtain ⟨k, P, acc', Q, rs, rp, hacc, sacc, uQ', sN', sA'⟩ := line_pairs ef hn a hv vne keep g sl lits ne hF
      refine ⟨_, ⟨Q.reverse ++ pr, acc', rfl, hacc, fun o => ?_, fun q mq => ?_, fun w => ?_, fun w => ?_⟩, ?_⟩
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
      · have : WithF E den (.tuple #[v, .atom "false"]) (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den (.tuple #[v, .atom "false"]) Q (eraseK a w) ∨
              WithF E den (.tuple #[v, .atom "false"]) pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sN', sN]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | ⟨L', mL', h⟩)
          · exact ⟨_, Or.inr rfl, h⟩
          · exact ⟨L', Or.inl mL', h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inr ⟨L', mL', h⟩
          · exact Or.inl h
      · have : WithF E den absF (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den absF Q (eraseK a w) ∨ WithF E den absF pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sA', sA]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨hk, h⟩ | ⟨hk, L', mL', h⟩)
          · exact ⟨hk, _, Or.inr rfl, h⟩
          · exact ⟨hk, L', Or.inl mL', h⟩
        · rintro ⟨hk, L', mL' | rfl, h⟩
          · exact Or.inr ⟨hk, L', mL', h⟩
          · exact Or.inl ⟨hk, h⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-0-/4», rs, rp, USort.rev2])
    (.tuple #[.nil, .tuple #[.map [], .atom "false"]])
    ⟨[], _, rfl, (none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o], by simp [UpdQ],
      fun w => by simp [withF_nil], fun w => by simp [withF_nil]⟩
  exact ⟨pr, F, run, hF, sF, uQ, sN, sA⟩


/-- The end of the general clause of `map_update_named_key/5`: grouping the pairs by field and putting each field. -/
theorem keep_tail (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) {v : Term} (hv : E v) (keep : Bool)
    (pairs : List Term) (hp : UpdQ E a (.tuple #[v, .atom "false"]) keep pairs) :
    ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (m + 1)) (Term.list pairs)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        let groups ← Erlang.lists.«foldl/3» (D (m + 1))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w)) ∨
        (w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w)) := by
  have hk : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey v f := fun q mq => by
    obtain ⟨f, b, rfl, hf, -⟩ := hp q mq
    exact ⟨f, b, rfl, hf.elim Or.inl fun h => Or.inr h.2⟩
  obtain ⟨entries, rg, inv⟩ := group_fold (m + 1) pairs hk
  obtain ⟨bdds, rb, fb, sb⟩ := group_bdds ef hm a hv pairs hp entries inv
  refine ⟨bdds, fun κ => ?_, fb, sb⟩
  simp [Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2», rg, Erlang.maps.«to_list/1», rb]


/-- The general clause of `map_update_named_key/5` with a constant, for `:keep` and `:reject`: the maps of the lines
whose key holds a value, with the key set to a value of the type, and with `:keep`, those without the key. -/
theorem keep_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (ow : Term) :
    ∃ (bdds : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") ow =
        .ok (.tuple #[Term.list bdds, F]) ∧ (∀ b ∈ bdds, MField E b) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ w (.atom a) = none ∧ ∃ L ∈ lines, InMLine den L w) := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5»
  simp only [modeT]
  split
  · rename_i h; simp at h
  · rename_i h _; cases keep <;> simp at h
  rotate_left
  · rename_i h₁ h₂ _; exact absurd rfl h₂
  -- Both paths give the pairs of the lines and their old field.
  have tail : ∀ (pairs : List Term) (F : Term), UpdQ E a (.tuple #[v, .atom "false"]) keep pairs →
      FieldValue E F → (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) →
      (∀ w, WithF E den (.tuple #[v, .atom "false"]) pairs (eraseK a w) ↔
        ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) →
      (∀ w, WithF E den absF pairs (eraseK a w) ↔ keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) →
      ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (n + 3)) (Term.list pairs)
          (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
        let groups ← Erlang.lists.«foldl/3» (D (n + 3))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (n + 3)) (.function false "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        (PutAt den v a w ∧ ∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ w (.atom a) = none ∧ ∃ L ∈ lines, InMLine den L w) := by
    intro pairs F hp hF sF sN sA
    obtain ⟨bdds, rb, fb, sb⟩ := keep_tail ef (m := n + 2) (by omega) a hv keep pairs hp
    refine ⟨bdds, rb, fb, fun w => (sb w).trans ?_⟩
    rw [sN]
    refine or_congr Iff.rfl ⟨fun ⟨hn, h⟩ => ?_, fun ⟨hk, hn, h⟩ => ⟨hn, (sA w).mpr ⟨hk, ?_⟩⟩⟩
    · obtain ⟨hk, L, mL, hL⟩ := (sA w).mp h
      have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      rw [e] at hL
      exact ⟨hk, hn, L, mL, hL⟩
    · have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      rw [e]; exact h
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
    obtain ⟨k', P, acc', Q, rs, rp, -, -, uQ, sN, sA⟩ := line_pairs ef (n := n + 1) (by omega) a hv vne keep g sl
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
      (fun w => by simpa using sN w) (fun w => by simpa using sA w)
    refine ⟨bdds, _, ?_, fb, fieldAt_ok ef g sl a, fun o => ?_, sb⟩
    · simp only [modeT] at rp rb
      simp only [rpop, rp, Lynx.Except.ok_bind]
      exact rb fun b => pure (.tuple #[b, fieldAt (.atom "open") l a])
    · rw [lit_values ef g a h₀ o]
      simp only [List.mem_singleton, exists_eq_left, LongM]
      exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
        fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩
  · -- Otherwise, the fold over the lines.
    obtain ⟨pr, F, runF, hF, sF, uQ, sN, sA⟩ := keep_fold ef hn a hv vne keep lines hl
    have revW : ∀ f u, WithF E den f pr.reverse u ↔ WithF E den f pr u := fun f u => by
      simp [WithF]
    obtain ⟨bdds, rb, fb, sb⟩ := tail pr.reverse F (fun q mq => uQ q (List.mem_reverse.mp mq)) hF sF
      (fun w => (revW _ _).trans (sN w)) (fun w => (revW _ _).trans (sA w))
    refine ⟨bdds, F, ?_, fb, hF, sF, sb⟩
    simp only [modeT] at runF rb
    simp only [pure_bind, runF, reverse1_list, Lynx.Except.ok_bind]
    exact rb fun b => pure (.tuple #[b, F])


/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a constant at an atom key, returning the old values: when a map
lacks the key, `badkey`, and otherwise the put of the key. -/
theorem keep_static_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (lines : List Term) (hne : lines ≠ [])
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((∃ L ∈ lines, LongM den L a none) → ∃ T Y, res = .tuple #[T, Y, Term.list [.tuple #[.atom "badkey", .atom a]],
        .atom "false"]) ∧
      ((¬∃ L ∈ lines, LongM den L a none) → ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ E T ∧
        (∀ x, den T x ↔ ∃ L ∈ lines, LongM den L a (some x)) ∧ PutMaps E den a (PutAt den v a) lines Y) := by
  classical
  obtain ⟨bdds, F, rb, fb, hF, sF, sb⟩ := keep_lines ef hn a hv vne keep lines hl (.atom "true")
  obtain ⟨t, o, rfl, ht⟩ := hF
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
  have optE : o = Bool.true ↔ ∃ L ∈ lines, LongM den L a none := by
    rw [← sF, fieldSem_mk]; simp
  have someE : ∀ x, den t x ↔ ∃ L ∈ lines, LongM den L a (some x) := fun x => by
    rw [← sF, fieldSem_mk]; simp
  obtain ⟨T, hT, rT, sT⟩ := ef.opt_union [] (m := n + 3) ht ef.none (by omega)
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  -- The old value and the errors: `badkey` when the old values are empty or a map lacks the key.
  have nk₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4))
      (.tuple #[.map [], .nil, .nil, .atom "false"]) (Term.list lines) (.cons (.atom a) .nil)
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
      (.atom "true") (.atom "true") (.atom "true") (.atom "true") =
      .ok (.tuple #[if e then Term.map [] else T, Term.list bdds,
        if (e || o) then Term.list [.tuple #[.atom "badkey", .atom a]] else .nil, boolAtom (!(e || o))]) := by
    have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok (.tuple #[Term.list bdds, .tuple #[t, boolAtom o]]) := rb
    cases keep <;> simp only [modeT, Bool.false_eq_true, ↓reduceIte] at rb' ⊢ <;> cases e <;> cases o <;>
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9», rb', re, Elixir.Module.Types.Descr.«opt_union/2»,
        rT, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, Lynx.Except.orElse]
    all_goals rw [show (Term.nil) = Term.list [] from rfl, append_list]; simp
  have nk₂ : ∀ acc, Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) acc (Term.list lines) .nil
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep])
      (.atom "false") (.atom "true") (.atom "true") (.atom "true") = .ok acc := fun acc => by
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.erlang.«not/1», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  obtain ⟨r, rr, fr, -, sr⟩ := munion_all (den := den) ef (m := n + 4) (by omega) (ok := fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) _ bdds (Nat.le_refl _) fun b mb => ⟨fb b mb, by
      rcases fb b mb with ⟨k, rfl⟩ | wb
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr (wb.mono fun _ _ => trivial)⟩
  have run : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 4)) bdd (Term.list lines)
      (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
      (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
      .ok (.tuple #[if e then Term.map [] else T, if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)],
        if (e || o) then Term.list [.tuple #[.atom "badkey", .atom a]] else .nil, boolAtom (!(e || o))]) := by
    unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
    cases keep <;> simp only [modeT, Bool.false_eq_true, ↓reduceIte] at nk₁ nk₂ ⊢ <;>
      simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Erlang.erlang.«==/2», Erlang.erlang.«/=/2»,
        Lynx.Term.isMember, Erlang.erlang.«--/2», Erlang.erlang.«++/2», Erlang.erlang.«not/1», Term.list,
        Term.properList?, nk₁, nk₂, Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3»,
        Erlang.erlang.«is_function/2», Erlang.lists.«map/2», rr] <;>
      split
    all_goals simp <;> assumption
  refine ⟨_, run, fun h => ⟨if e then Term.map [] else T,
    if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)], ?_⟩, fun h => ?_⟩
  · have : (e || o) = Bool.true := by simp [optE.mpr h]
    simp [this]
  have ho : o = Bool.false := by
    cases o
    · rfl
    · exact absurd (optE.mp rfl) h
  have he : e = Bool.false := by
    cases e
    · rfl
    · -- No map holds a value at the key, and none lacks it: there are no maps.
      obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
      obtain ⟨w, hw⟩ := (hl L mL).2
      cases wa : w (.atom a) with
      | none => exact absurd ⟨L, mL, w, hw, wa⟩ h
      | some x => exact absurd ((someE x).mpr ⟨L, mL, w, hw, wa⟩) (se.mp rfl x)
  subst ho he
  refine ⟨T, if r = .atom "bdd_bot" then Term.map [] else .map [(.atom "map", r)], by simp, hT, fun x => by rw [sT, someE]; simp [nonx], r, fr, ?_, fun w => ?_⟩
  · by_cases bot : r = .atom "bdd_bot"
    · subst bot; exact Or.inr ⟨by simp, fun w => denMF_bot w⟩
    · exact Or.inl (by simp [bot])
  · rw [sr, sb]
    constructor
    · rintro (⟨hp, L, mL, x, hL⟩ | ⟨-, hn, L, mL, hL⟩)
      · exact ⟨hp, L, mL, _, hL⟩
      · exact absurd ⟨L, mL, w, hL, hn⟩ h
    · rintro ⟨hp, L, mL, o', hL⟩
      cases o' with
      | some x => exact Or.inl ⟨hp, L, mL, x, hL⟩
      | none => exact absurd ⟨L, mL, _, hL, by simp [setK]⟩ h

theorem longM_iff {b : Term} {lines : List Term}
    (inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (a : String) (o : Option V) :
    (∃ L ∈ lines, LongM den L a o) ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = o :=
  ⟨fun ⟨L, mL, w, hw, wa⟩ => ⟨w, (inB w).mpr ⟨L, mL, hw⟩, wa⟩,
    fun ⟨w, hw, wa⟩ => by obtain ⟨L, mL, hL⟩ := (inB w).mp hw; exact ⟨L, mL, w, hL, wa⟩⟩

/-- `map_update_static/5` for `:keep` and `:reject` of a constant at an atom key, returning the old values. -/
theorem keep_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 4)) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") (.atom "true") =
        .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (∃ w, denMF E den b w = Bool.true) ∧
        ((∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, Y, Term.list [.tuple #[.atom "badkey", .atom a]], .atom "false"]) ∧
        ((¬∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, Y, .nil, .atom "true"] ∧ E T ∧
          (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = some x) ∧
          PutField E den a (PutAt den v a) b Y)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      obtain ⟨res, rY, hbad, hgood⟩ := keep_static_dnf ef hn a hv vne keep (.tuple #[.integer k, tag, fieldsTerm l]) _
        (by simp) hl
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      refine ⟨res, ?_, Or.inr ⟨⟨w₀, (sem w₀).mpr h₀⟩, fun h => hbad ((longM_iff inB a none).mpr h), fun h => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
        simpa [Term.list] using rY
      · obtain ⟨T, Y, rfl, hT, sT, pY⟩ := hgood fun h' => h ((longM_iff inB a none).mp h')
        exact ⟨T, Y, rfl, hT, fun x => (sT x).trans (longM_iff inB a (some x)), putMaps_field inB pY⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
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
      obtain ⟨res, rY, hbad, hgood⟩ := keep_static_dnf ef hn a hv vne keep b (L :: rest) (by simp) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨res, ?_, Or.inr ⟨⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩,
        fun h => hbad ((longM_iff inB a none).mpr h), fun h => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · obtain ⟨T, Y, rfl, hT, sT, pY⟩ := hgood fun h' => h ((longM_iff inB a none).mp h')
        exact ⟨T, Y, rfl, hT, fun x => (sT x).trans (longM_iff inB a (some x)), putMaps_field inB pY⟩


section
variable {t : Term} {n : Nat}

/-- `map_update_unchecked/4` for `:keep` and `:reject` of a static value at an atom key of static types of the next
level, returning the old values: `:badmap` unless the type holds only maps, `badkey` when one of them lacks the key, and
otherwise the put of the key. -/
theorem keep_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x) (keep : Bool) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (.tuple #[Term.list [.atom a], .nil, .atom "nil", .nil, .nil])
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], modeT keep]) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        MOnly t n X ∧
        ((∃ w, MT t n X w ∧ w (.atom a) = none) →
          res = .tuple #[.atom "error", Term.list [.tuple #[.atom "badkey", .atom a]]]) ∧
        ((¬∃ w, MT t n X w ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
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
    have rE := next_empty dR (m := k + 4) (by omega)
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
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    have lack : (∃ w, MT t n X w ∧ w (.atom a) = none) ↔
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true ∧ w (.atom a) = none :=
      ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩⟩
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨⟨w₀, hw₀⟩, hbad, hgood⟩⟩ :=
        keep_update_static (level t n).ef (n := k) (by omega) a hv vne keep hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      by_cases hl : ∃ w, MT t n X w ∧ w (.atom a) = none
      · obtain ⟨T, Y, rfl⟩ := hbad (lack.mp hl)
        refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun _ => rfl, fun h => absurd hl h⟩⟩
        simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
      · obtain ⟨T, Y, rfl, hT, sT, r, fr, hY, sr⟩ := hgood fun h => hl (lack.mpr h)
        have semT : ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x := fun x => by
          rw [sT]; exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mpr hw, wa⟩, fun ⟨w, hw, wa⟩ => ⟨w, (mt w).mp hw, wa⟩⟩
        have sem : ∀ w, denMF (level t n).E (level t n).den r w = Bool.true ↔
            PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w) := fun w => by
          rw [sr]
          exact and_congr Iff.rfl ⟨fun ⟨o, h⟩ => ⟨o, (mt _).mpr h⟩, fun ⟨o, h⟩ => ⟨o, (mt _).mp h⟩⟩
        rcases hY with rfl | ⟨rfl, emp⟩
        · refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun h => absurd h hl, fun _ =>
            ⟨T, _, rfl, hT, semT, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_⟩⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
          · rw [denD_map] at hq
            by_cases e : q.1.1 = "map"
            · exact e
            · simp [mapLookup, e, dn_none] at hq
          · rw [← sem]; simp [MT, mapLookup]
        · refine ⟨_, ?_, Or.inr ⟨only.mpr ⟨restE, w₀, hw₀⟩, fun h => absurd h hl, fun _ =>
            ⟨T, _, rfl, hT, semT, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_⟩⟩⟩
          · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
          · rw [denD_map] at hq
            simp [mapLookup, dn_none] at hq
          · rw [← sem, emp w]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

/-- `map_update/5` for `:keep` and `:reject` of a static value at a single atom key, returning the old values. -/
theorem update_keep {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {v : Term}
    (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) (keep : Bool) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) (atomT a) v (modeT keep) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        MOnly t n X ∧
        ((∃ w, MT t n X w ∧ w (.atom a) = none) →
          res = .tuple #[.atom "error", Term.list [.tuple #[.atom "badkey", .atom a]]]) ∧
        ((¬∃ w, MT t n X w ∧ w (.atom a) = none) →
          ∃ T Y, res = .tuple #[T, .map Y, .nil] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ w (.atom a) = some x) ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∀ w, MT t n Y w ↔ PutAt (level t n).den v a w ∧ ∃ o, MT t n X (setK a o w))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨res, run, h⟩ := keep_map hX a hv vne keep hm
  refine ⟨res, ?_, h⟩
  unfold Elixir.Module.Types.Descr.«map_update/5»
  simp only [modeT] at run ⊢
  rcases sv with rfl | ⟨Z, rfl, sZ⟩ <;> cases keep
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at run
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      Lynx.Term.getMapKeys]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]
  · simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», split_one, run,
      getMapKeys_single, sZ]

end

end Elixir.STTDescrProofsTest.Nest
