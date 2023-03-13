From Coq Require Import Reals Streams.
From mathcomp Require Import all_ssreflect all_algebra.
From Coquelicot Require Import Coquelicot.

(*TODO:
  1) A universal lt_x_y lemma
  2) How to use mathcomp-analysis Lebesgue integral??
  3) Check t_initial and traj t for t < t_initial
*)

Open Scope ring_scope.
Open Scope R_scope.

Section SwitchedSystem.

Structure switched_system : Type := BuildSwitchedSystem {
  dimension: nat;
  modes_count: nat;                                      
  modes: modes_count .-tuple ('cV[R]_dimension -> 'cV[R]_dimension);
  switches: Stream (R * 'I_modes_count);                       
}.

Lemma lt_0_1: is_true (0 < 1)%N. Proof. by []. Qed.
Definition o0 : 'I_1 := Ordinal lt_0_1.

Fixpoint finite_approx A (s: Stream A) (n: nat) : seq A :=
  match n with
  | S n' =>
      match s with
      | Streams.Cons h t => h :: finite_approx A s n'
      end
  | O => nil
  end.

Definition switches_finite_approx (s: switched_system) :=
  {approx: seq(R * 'I_(modes_count s)) | finite_approx _ (switches s) (size approx) = approx}.

Definition approx_is_before (s: switched_system) (approx: switches_finite_approx s) (t:R) :=
  foldr (fun switch_i p => (fst switch_i) < t /\ p) True (proj1_sig approx).

Definition has_all_switches_before (s: switched_system) (approx: switches_finite_approx s) (t:R) :=
   approx_is_before s approx t /\
     forall l', approx_is_before s l' t /\ ((size (proj1_sig l')) <= (size (proj1_sig approx)))%N.

Fixpoint sum_of_integrals_helper
  (s: switched_system)
  (approx: seq (R * 'I_(modes_count s)))
  (traj: R -> 'cV[R]_(dimension s))
  (x_initial: 'cV[R]_(dimension s)) : 'cV[R]_(dimension s) :=

  match approx with
  | (t1, mode) :: (t2, _) :: tail =>
      \col_(i < (dimension s))
       (
          (sum_of_integrals_helper s tail traj x_initial) i o0 +
          RInt (fun (t:R) => ((tnth (modes s) mode) (traj t)) i o0) t1 t2
       )
  | (t, _) :: nil => x_initial 
  | nil => x_initial
  end.

Definition trajectory_helper
  (s: switched_system)
  (approx: seq (R * 'I_(modes_count s)))
  (traj: R -> 'cV[R]_(dimension s))
  (x_initial: 'cV[R]_(dimension s))
  (t:R) : 'cV[R]_(dimension s) :=

  match approx with
  | (last_t, last_mode) :: tail =>
  \col_(i < (dimension s))
  (                                 
    (sum_of_integrals_helper s approx traj x_initial) i o0 +
    RInt (fun (tau:R) => ((tnth (modes s) last_mode) (traj tau)) i o0) last_t t
  )
  | nil => x_initial
  end.            

Definition is_caratheodory_trajectory
  (s: switched_system)
  (traj: R -> 'cV[R]_(dimension s))
  (x_initial: 'cV[R]_(dimension s)) :=
  
  forall (t:R),
  exists approx,
    has_all_switches_before s approx t ->
    traj t = trajectory_helper s (proj1_sig approx) traj x_initial t.                             

End SwitchedSystem.

Section SwitchedSystemExample. 
  
Definition mode1 (x: 'cV[R]_2) : 'cV[R]_2 :=
  \col_(i < 2) nth 0 [:: 2; 1] i.

Definition mode2 (x: 'cV[R]_2) : 'cV[R]_2 :=
  \col_(i < 2) nth 0 [:: -2; -1] i.

Parameter example_trajectory: R -> 'cV[R]_2.

Lemma lt_0_2 : is_true(0 < 2)%N. Proof. by []. Qed.
Lemma lt_1_2 : is_true (1 < 2)%N. Proof. by []. Qed.
Lemma bool_le_2 b : (nat_of_bool b < 2)%N.
Proof. by case: b.  Qed.

Definition controller_example (t: R) : (R * 'I_2) :=
  let x1 := (example_trajectory t) (Ordinal lt_0_2) (Ordinal lt_0_1) in
  let x2 := (example_trajectory t) (Ordinal lt_1_2) (Ordinal lt_0_1) in
  if cond_positivity (x2 + 2 * x1) then (t + 1, Ordinal lt_0_2) else (t + 1, Ordinal lt_1_2).

CoFixpoint switching_points_example (t: R): Stream (R * 'I_2) :=
  let (t_next, m_next) := controller_example t in
  Streams.Cons (t, m_next) (switching_points_example t_next).
  
Definition switched_example :=
  BuildSwitchedSystem 2 2 [tuple mode1; mode2] (switching_points_example 0).   
  
Definition periodic A (f: R -> A) (T:R) := forall t, f(t + T) = f(t).

Definition example_trajectory_value :=
  periodic _ example_trajectory 2 /\
  forall (t:R),
    0 <= t <= 1 -> example_trajectory t = \col_(i < 2) nth 0 [:: -2*t + 1; -t + 0.5] i /\
    1 < t <= 2  -> example_trajectory t = \col_(i < 2) nth 0 [:: 2*t -1; t - 0.5] i.                

Definition initial_point := \col_(i < 2) nth 0 [:: 1; 0.5] i.

Definition example_approx (t:R) :=
  if cond_positivity(t) then
    finite_approx _ (switches switched_example) (Z.abs_nat (floor t))
  else nil.

Theorem example_approx_is_approx :
  forall (t:R),
    finite_approx _ (switches switched_example) (size (example_approx t)) = (example_approx t).
Proof.
  intros t.
  unfold example_approx.
  destruct (cond_positivity t).
  * simpl.
    assert (forall A s len, size (finite_approx A s len) = len). {
      intros A s len.
      induction len.
      * unfold finite_approx. simpl. reflexivity.
      * unfold finite_approx. destruct s. fold finite_approx. simpl. rewrite IHlen. reflexivity.
    }
    rewrite H. reflexivity.
  * simpl. reflexivity.
Qed.

Theorem check_trajectory :
  example_trajectory_value -> is_caratheodory_trajectory switched_example example_trajectory initial_point.
Proof.
  intros Hvalue.
  unfold is_caratheodory_trajectory.
  intros t.
  exists (exist
            (fun a => finite_approx (R * 'I_(modes_count switched_example)) (switches switched_example) (size a) = a)
            (example_approx t) (example_approx_is_approx t)).
  simpl.
Abort.  
  
End SwitchedSystemExample.


