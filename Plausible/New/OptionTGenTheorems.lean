import Plausible.IR.Examples
import Plausible.New.OptionTGen
import Plausible.New.ArbitrarySizedSuchThat
import Plausible.New.DecOpt
import Lean
import Plausible.Gen
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat
open Lean Elab Tactic Meta PrettyPrinter

theorem pure_gen (h: Gen.run (pure ret) size st1 = EStateM.Result.ok val st2) : ret = val :=by
  simp [Gen.run, runRand, bind, EStateM.bind] at h
  split at h; split at h; split at h
  any_goals contradiction
  simp [pure, EStateM.pure] at h
  rename_i heq _ _ _ _
  simp [StateT.run, liftM, monadLift, pure, EStateM.pure, StateT.pure, Id.run ] at heq
  simp [← heq.left] at h; exact h.left

def GenEnsure (gen: Gen α) (p: α → Prop) (_: gen.run size u1 = EStateM.Result.ok v st2) := p v

def OptionTGenEnsureRun  (p: α → Prop) (ogen: OptionT Gen α)
      := ∀ size v u1 u2,  ((ogen.run.run size).run u1 = EStateM.Result.ok (some v) u2) →  p v

def OptionTGenEnsure  (p: α → Prop) (ogen: OptionT Gen α)
      := ∀ size v stg1 stg2, ogen {down:=size} stg1 = (some v, stg2) →  p v

def OptionTGenListEnsure  (p: α → Prop) (ogens: List (OptionT Gen α))
      := ∀ ogen ∈ ogens, OptionTGenEnsure p ogen

theorem OptionTGenEnsure_of_fail: OptionTGenEnsure p OptionT.fail :=by
  simp [OptionTGenEnsure, OptionT.fail, OptionT.mk, pure, ReaderT.pure, StateT.pure ]
  intros; injections

theorem OptionTGenListEnsure_tail (h: OptionTGenListEnsure p (x::xs)) : OptionTGenListEnsure p xs :=by
  unfold OptionTGenListEnsure at *
  intro ogen h0
  have h1: ogen ∈ x::xs := by simp only [List.mem_cons, h0, or_true]
  exact h ogen h1

theorem OptionTGenListEnsure_subset
      (h: OptionTGenListEnsure p xs1) (hs: ∀ x ∈ xs, x ∈ xs1):
      OptionTGenListEnsure p xs :=by
  unfold OptionTGenListEnsure at *
  intro ogen h0
  simp_all only

theorem OptionTGenListEnsure_append
      (h1: OptionTGenListEnsure p xs1)
      (h2: OptionTGenListEnsure p xs2):
      OptionTGenListEnsure p (xs1.append xs2) :=by
  unfold OptionTGenListEnsure at *
  intro ogen h0
  simp at h0
  by_cases hc: ogen ∈ xs1
  simp_all only [true_or]
  simp_all only [false_or]

def OptionTGen_run_exists {α size u1 v u2} {ogen: OptionT Gen α} (h: (ogen.run.run size).run u1 = EStateM.Result.ok (some v) u2)
      : ∃ stg1 stg2, ogen {down:=size} stg1 = (some v, stg2) :=by
  simp only [EStateM.run, Gen.run, runRand, bind, EStateM.bind, ReaderT.run, OptionT.run] at h
  split at h; split at h; split at h;
  any_goals contradiction
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
  rename_i he _ _ _ _
  simp only [StateT.run, liftM, monadLift, pure, EStateM.pure, Id.run,
    EStateM.Result.ok.injEq] at he
  rename_i a2 _ _ _ a1 _ _ _ _ _
  exists {down := a2}; exists a1.snd
  rw[he.left]; simp[← h.left]

theorem OptionTGenEnsureRun_of_OptionTGenEnsure: OptionTGenEnsure p ogen → OptionTGenEnsureRun p ogen :=by
  intro h
  unfold OptionTGenEnsureRun
  intro size v u1 u2 h0
  have ⟨stg1, stg2, h0⟩  := OptionTGen_run_exists h0
  unfold OptionTGenEnsure at h
  exact h size v stg1 stg2 h0

theorem OptionTGenEnsure_thunkgen: OptionTGenEnsure p gen ↔ OptionTGenEnsure p (OptionTGen.thunkGen fun _ => gen) :=by
  simp only [thunkGen]

theorem OptionTGenEnsure_pure:  OptionTGenEnsure p (pure v) ↔ p v :=by
  simp only [pure, OptionT.pure, OptionT.mk]
  unfold ReaderT.pure
  simp only [pure]; unfold StateT.pure ; simp only [pure]
  unfold OptionTGenEnsure
  simp only [forall_const]
  constructor
  have k := StdGen.mk 0 0
  intro h; have h:= h v {down:= k} {down:= k} ; simp only [forall_const] at h; exact h
  intros; injections; simp_all only

theorem OptionTGenEnsure_OptionTBind {genn: OptionT Gen β} {f: β → OptionT Gen α}
    (h: ogen = OptionT.bind genn f) (hfa: ∀ b, OptionTGenEnsure p (f b)) : OptionTGenEnsure p ogen :=by
  simp [OptionT.bind, OptionT.mk, bind] at h;
  unfold ReaderT.bind at h; simp only [bind] at h
  unfold StateT.bind at h; simp only [bind] at h
  unfold OptionTGenEnsure; intro size v stg1 stg2 h0
  simp only [h] at h0
  split at h0; split at h0
  rename_i stg _ n hg
  unfold OptionTGenEnsure at hfa
  exact hfa n size v stg stg2 h0
  simp [pure, ReaderT.pure, StateT.pure] at h0
  injections

theorem OptionTGenEnsure_bind_forall {genn: OptionT Gen β} {f: β → OptionT Gen α}
    (hfa: ∀ b, OptionTGenEnsure p (f b)) : OptionTGenEnsure p (bind genn f) :=by
  simp only [bind, OptionT.bind, OptionT.mk] ;
  unfold ReaderT.bind; simp only [bind]
  unfold StateT.bind; simp only [bind]
  unfold OptionTGenEnsure; intro size v stg1 stg2 h0
  simp only at h0
  split at h0; split at h0
  rename_i stg _ n hg
  unfold OptionTGenEnsure at hfa
  exact hfa n size v stg stg2 h0
  simp [pure, ReaderT.pure, StateT.pure] at h0
  injections

theorem OptionTGenEnsure_bind {gen_a: OptionT Gen α} {f: α → OptionT Gen β}
    pa pb
    (ha: OptionTGenEnsure pa gen_a)
    (hfa: ∀ a, (pa a) → OptionTGenEnsure pb (f a)) : OptionTGenEnsure pb (bind gen_a f) :=by
  simp only [bind, OptionT.bind, OptionT.mk] ;
  unfold ReaderT.bind; simp only [bind]
  unfold StateT.bind; simp only [bind]
  unfold OptionTGenEnsure; intro size v stg1 stg2 h0
  simp only at h0
  split at h0; split at h0
  rename_i stg _ a hg
  unfold OptionTGenEnsure at ha
  have ha:= ha size a stg1 stg hg
  have hfa:= hfa a ha
  unfold OptionTGenEnsure at hfa
  exact hfa size v stg stg2 h0
  simp [pure, ReaderT.pure, StateT.pure] at h0
  injections

theorem OptionTGenEnsure_trycatch {a: OptionT Gen α} {p: α → Prop }
      (ha: OptionTGenEnsure p a) (hb: OptionTGenEnsure p b)
          : OptionTGenEnsure p (OptionT.tryCatch a (fun _ => b)) :=by
  simp only [OptionT.tryCatch, OptionT.mk, bind]
  unfold ReaderT.bind
  simp only [bind]; unfold StateT.bind; simp only [bind];
  unfold OptionTGenEnsure at *
  intro size v u1 u2
  intro h; simp only at h
  split at h; split at h;
  simp [pure, ReaderT.pure, StateT.pure] at h
  rename_i _ ua _ ra ga
  have ha:= ha size ra u1 ua ga
  injections; rename_i h; rw[← h]; exact ha
  rename_i  _ ub _ _ _
  exact hb size v ub u2 h

theorem pickDrop_fst_mem (h: (pickDrop xs k).2.fst ≠ OptionT.fail): (pickDrop xs k).2.fst ∈ xs.unzip.snd :=by
  induction xs generalizing k
  simp [pickDrop] at h
  rename_i head tail ind
  simp only [pickDrop]
  split; simp only [List.unzip_cons, List.unzip_fst, List.unzip_snd, List.mem_cons, List.mem_map,
    Prod.exists, exists_eq_right, true_or];
  simp only [pickDrop]
  have : (pickDrop tail (k - head.fst)).2.fst ∈ tail.unzip.snd :=by
    apply ind
    simp [pickDrop] at h; split at h; contradiction; simp at h; simp only [ne_eq, h,
      not_false_eq_true]
  have g : (head :: tail).unzip.snd = head.snd::tail.unzip.snd :=by simp only [List.unzip_cons,
    List.unzip_fst, List.unzip_snd]
  simp only [g, List.mem_cons]; apply Or.inr this

theorem OptionTGenEnsure_pickDrop (h: OptionTGenListEnsure p xs.unzip.2): OptionTGenEnsure p (pickDrop xs k).2.fst:=by
  by_cases hc: (pickDrop xs k).2.fst =OptionT.fail
  rw[hc]; exact OptionTGenEnsure_of_fail
  have hc:= pickDrop_fst_mem hc;
  exact h (pickDrop xs k).snd.fst hc

theorem pickDrop_snd_subset (h: x ∈ (pickDrop xs k).2.snd.unzip.snd) : x ∈ xs.unzip.snd :=by
  induction xs generalizing k
  simp [pickDrop] at h
  rename_i head tail ind
  have g : (head :: tail).unzip.snd = head.snd::tail.unzip.snd :=by simp only [List.unzip_cons,
    List.unzip_fst, List.unzip_snd]
  simp only [g, List.mem_cons];
  simp only [pickDrop, List.unzip_snd] at h
  split at h
  have : x ∈ tail.unzip.2 := by simp[h]
  apply Or.inr this
  by_cases hc: x = head.snd; simp[hc];
  simp only [List.map_cons, List.mem_cons, hc, false_or] at h
  apply Or.inr
  apply @ind (k - head.fst)
  simp[h]

theorem OptionTGenEnsure_backtrackfuel (h: OptionTGenListEnsure p xs.unzip.2)
        : OptionTGenEnsure p (backtrackFuel fuel total xs) :=by
  induction fuel generalizing total xs
  simp [backtrackFuel, OptionTGenEnsure, OptionT.fail, OptionT.mk, pure, ReaderT.pure, StateT.pure];
  intros; injections;
  rename_i size ind
  simp [backtrackFuel]; apply OptionTGenEnsure_bind_forall
  intro b
  apply OptionTGenEnsure_trycatch; apply OptionTGenEnsure_pickDrop; assumption
  apply ind
  apply OptionTGenListEnsure_subset h
  apply pickDrop_snd_subset

theorem OptionTGenEnsure_backtrack (h: OptionTGenListEnsure p xs.unzip.2)
      : OptionTGenEnsure p (backtrack xs) :=by
  unfold backtrack
  apply OptionTGenEnsure_backtrackfuel h
