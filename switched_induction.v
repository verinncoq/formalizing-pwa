From Coq Require Import Reals List Lia Lra.
Import ListNotations.
From Coquelicot Require Import Coquelicot.
From CoqE2EAI Require Import piecewise_linear missing_lemmas.

Open Scope R_scope.

(*---------------------------------------------------------------------------*)

Section SwitchedSystem.

Structure switched_system : Type := BuildSwitchedSystem {
  dimension: nat;                                
  modes: list (colvec dimension -> colvec dimension);
  switches: R -> list (R * nat);       
  switches_correct:   
    forall t,
      let l := switches t in
      forall switch, 
        In switch l -> (snd switch < length modes)%nat   
}.

Definition is_mode_solution
  (s: switched_system)
  (mode_idx: nat)
  (t_from t_to: R)
  (x_t_from: colvec (dimension s))
  (solution: R -> colvec (dimension s)) :=
  forall mode t d,
    (mode_idx < length (modes s))%nat ->
    mode = nth mode_idx (modes s) d ->
    t_from <= t <= t_to ->
    solution t = mk_colvec (dimension s)
       (
          fun i =>
            RInt (fun tau => coeff_colvec 0 (mode (solution tau)) i) t_from t
                               + coeff_colvec 0 x_t_from i
       ).

Definition mode_solver (s:switched_system) :=
  {solver : nat -> R -> R -> colvec (dimension s) -> (R -> colvec (dimension s)) |
    forall mode_idx t_from t_to x_t_from,
      is_mode_solution s mode_idx t_from t_to x_t_from (solver mode_idx t_from t_to x_t_from) }.


Fixpoint traj_on_switches_helper
  (s: switched_system)
  (switches: list (R * nat))
  (x_init: colvec (dimension s))
  (solver: mode_solver s): colvec (dimension s)
  :=
  match switches with
  | nil => x_init
  | (t2, m2) :: tail =>
      match tail with
      | nil => x_init
      | (t1, m1) :: _ =>
          match solver with
          | exist solver_func _  =>
              let traj_at_t1 := (traj_on_switches_helper s tail x_init solver) in
              mk_colvec (dimension s) (fun i =>
                coeff_colvec 0 ((solver_func m1 t1 t2 traj_at_t1) t2) i
              )                                             
          end
      end
  end.

Definition trajectory
  (s: switched_system)
  (x_init: colvec (dimension s))
  (solver: mode_solver s)
  (t:R)
  : colvec (dimension s) :=
  let latest_switches := (switches s) t in
  match latest_switches with
  | nil => x_init
  | (latest_t, latest_m) :: tail =>
      let traj_at_last_switch := traj_on_switches_helper s latest_switches x_init solver in
      match solver with
      | exist solver_func _ =>
          (solver_func latest_m latest_t t traj_at_last_switch) t 
     end
  end.

End SwitchedSystem.

Section SwitchedSystemProperties.

(*---------------------------------------------------------------------------*)

Section SwitchedSystemExample. 
  
Definition mode1 (x: colvec 2) := mk_colvec 2 (
    fun i =>
        match i with
        | 0 => 2
        | 1 => 1
        | _ => 0
        end
).

Definition mode2 (x: colvec 2) := mk_colvec 2 (
  fun i =>
      match i with
      | 0 => -2
      | 1 => -1
      | _ => 0
      end
).

Parameter observable_trajectory: R -> colvec 2.

Definition controller (current_x: colvec 2): nat :=
  let x1 := coeff_colvec 0 current_x 0 in
  let x2 := coeff_colvec 0 current_x 1 in  
  match cond_positivity (x2 + 2 * x1) with
    | true  => 1%nat
    | false => 0%nat
  end.

Fixpoint generate_switches (len: nat): list (R * nat) :=
  let lenR := INR len in
  match len with
  | 0 => (0, 1%nat) :: nil
  | S n =>
      let traj_t := observable_trajectory lenR in
      (lenR, controller traj_t) :: generate_switches n
  end.

Theorem generate_switches_Sn:
  forall len,
    let lenR := INR len in
    let traj_t := observable_trajectory lenR in
    generate_switches (S len) = (lenR, controller traj_t) :: generate_switches len.
Proof.
Admitted.

Definition switches_before (t: R): list (R * nat) :=
  if Rle_lt_dec t 0 then
    nil
  else
    generate_switches (Z.abs_nat (floor1 t)).

Theorem switches_before_correct:
  forall t,
    let l := switches_before t in
    forall switch, 
      In switch l -> (snd switch < 2)%nat.
Proof. 
  intros t l switch Hswitch.
  unfold switches_before in l.
  unfold l in Hswitch.
  destruct Rle_lt_dec as [H0|Hgt].
  - contradiction Hswitch. 
  - induction (Z.abs_nat (floor1 t)).
    * simpl in Hswitch.
      destruct Hswitch.
      rewrite <- H. simpl. lia.
      contradiction.
    * unfold generate_switches in Hswitch.
      unfold controller in Hswitch.
      remember (cond_positivity
      (coeff_colvec 0 (observable_trajectory (INR (S n))) 1 +
      2 * coeff_colvec 0 (observable_trajectory (INR (S n))) 0)) as positive.
      destruct positive.
      fold generate_switches in l.
      simpl in Hswitch.
      destruct Hswitch.
      * rewrite <- H. simpl. lia.
      * apply IHn. apply H.
      fold generate_switches in l.
      destruct Hswitch.
      * rewrite <- H. simpl. lia.
      * apply IHn. apply H.
Qed. 
  
Definition switched_example :=
  BuildSwitchedSystem 2 [mode1; mode2] switches_before switches_before_correct.   

Definition mode1_solution (t: R) (x_init: colvec 2) := mk_colvec 2 (
    fun i =>
        match i with
        | 0 => 2*t + coeff_colvec 0 x_init 0
        | 1 => t + coeff_colvec 0 x_init 1
        | _ => 0
        end
).

Definition mode2_solution (t: R) (x_init: colvec 2) := mk_colvec 2 (
  fun i =>
      match i with
      | 0 => -2*t + coeff_colvec 0 x_init 0
      | 1 => -t + coeff_colvec 0 x_init 1
      | _ => 0
      end
).

Definition example_mode_solver_implementation
  (mode_idx: nat)
  (t_from t_to: R)
  (x_t_from: colvec 2): R -> colvec 2 :=
  match mode_idx with
  | 0 => (fun t => mode1_solution (t - t_from) x_t_from)
  | 1 => (fun t => mode2_solution (t - t_from) x_t_from)
  | _ => (fun t => null_vector 2)
  end.

Theorem example_mode_solver_correct: 
  forall mode_idx t_from t_to x_t_from,
    is_mode_solution
      switched_example mode_idx t_from t_to x_t_from
      (example_mode_solver_implementation mode_idx t_from t_to x_t_from).
Proof.
  unfold is_mode_solution.
  intros mode_idx t_from t_to x_t_from mode t d Hmodeidx Hmode Ht.
  unfold example_mode_solver_implementation.
  destruct mode_idx.
  * unfold mode1_solution.
    unfold mk_colvec.
    apply mk_matrix_ext.
    intros i j Hi Hj. 
    rewrite Hmode.
    unfold switched_example. 
    unfold mode1.
    simpl.
    unfold coeff_colvec.
    unfold mk_colvec.
    simpl in Hi.
    rewrite coeff_mat_bij.
    rewrite RInt_const.
    destruct i.
    - compute. rewrite Rmult_comm. reflexivity.
    destruct i.
    - rewrite <- (Rmult_1_r (t - t_from)) at 1.
      compute. reflexivity.
      compute in Hi. lia.
      apply Hi. lia.
  * destruct mode_idx.
    unfold mode2_solution.
    unfold mk_colvec.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    rewrite Hmode.
    unfold switched_example.
    unfold mode2.
    unfold coeff_colvec.
    unfold mk_colvec.
    simpl. simpl in Hi.
    rewrite coeff_mat_bij.
    rewrite RInt_const.
    destruct i.
    - compute. rewrite Rmult_comm. reflexivity.
    destruct i.
    - rewrite <- (Rmult_1_r (- (t - t_from))).
      compute. 
      rewrite <- Ropp_mult_distr_l.
      rewrite <- Ropp_mult_distr_r.
      reflexivity. lia. lia. lia.
    simpl in Hmodeidx. lia.
Qed.

Definition example_mode_solver: mode_solver switched_example := 
  exist _ example_mode_solver_implementation example_mode_solver_correct.         

Definition initial_point := mk_colvec 2 (
  fun i =>
    match i with
    | 0 => 1 
    | 1 => 0.5
    | _ => 0
    end
).

Theorem trajectory_until_0: 
    forall t, (t < 0) ->
      trajectory switched_example initial_point example_mode_solver t = initial_point.
Proof.
    intros t Ht_lt_0.
    unfold trajectory.
    unfold switched_example. 
    unfold switches.
    unfold switches_before.
    destruct Rle_lt_dec; try lra.
    reflexivity.
Qed.

Theorem trajectory_0_1: 
  forall t,
    (0 <= t <= 1) ->
    trajectory switched_example initial_point example_mode_solver t = mk_colvec 2 (
      fun i =>
        match i with
        | 0 => -2 * t + 1
        | 1 => -t + 0.5
        | _ => 0
        end
    ).
Proof.
  intros t Ht.
  unfold trajectory.
  simpl.
  unfold switches_before.
  destruct Rle_lt_dec.
  * unfold initial_point.
    rewrite (Rle_antisym t 0); try lra.
    unfold mk_colvec. apply mk_matrix_ext.
    intros i j Hi Hj. induction j; try lia.
    repeat (induction i; try lra).
  * assert (Habs: Z.abs_nat (floor1 t) = 0%nat). {
        unfold Z.abs_nat.
        rewrite (floor1_tech _ 0%Z); try lra.
        reflexivity.
    }
    rewrite Habs. simpl.
    rewrite Rminus_0_r.
    unfold mode2_solution.
    reflexivity.
Qed.

Theorem trajectory_1_2: 
    forall t,
      let traj_t := trajectory switched_example initial_point example_mode_solver in
      observable_trajectory = traj_t ->
      (1 < t <= 2) ->
      traj_t t = mk_colvec 2 (
        fun i =>
          match i with
          | 0 => 2 * t - 3
          | 1 => t - 1.5
          | _ => 0
          end
      ).
Proof.
    intros t traj_t Hobservable Ht.
    unfold traj_t. unfold trajectory.
    simpl.
    unfold switches_before.
    destruct Rle_lt_dec; try lra.
    assert (Habs: Z.abs_nat (floor1 t) = 1%nat). {
      unfold Z.abs_nat. 
      rewrite (floor1_tech _ 1); try lra.
      compute. reflexivity. 
    }
    rewrite Habs. unfold generate_switches. unfold controller. simpl.
    assert (Hobstraj_pos: cond_positivity 
      (coeff_colvec 0 (observable_trajectory 1) 1 + 
      2 * coeff_colvec 0 (observable_trajectory 1) 0) = false). {
      unfold cond_positivity.
      destruct Rle_dec as [Hn|Hr]. 
      * exfalso.
        rewrite Hobservable in Hn.
        unfold traj_t in Hn.
        rewrite trajectory_0_1 in Hn.
        unfold coeff_colvec in Hn. unfold mk_colvec in Hn.
        repeat (rewrite coeff_mat_bij in Hn; try lia).
        all: lra. 
    }
    rewrite Hobstraj_pos.
    unfold example_mode_solver_implementation.
    unfold mode1_solution.
    unfold traj_on_switches_helper.
    unfold example_mode_solver.
    unfold example_mode_solver_implementation.
    unfold mode2_solution.
    unfold initial_point. unfold coeff_colvec. unfold mk_colvec. 
    repeat (rewrite coeff_mat_bij; try simpl; try lia).
    apply mk_matrix_ext.
    intros i j Hi Hj.
    induction j; try lia.
    induction i.
    * lra.     
    induction i.
    * lra.
    * lia. 
Qed.

Theorem trajectory_periodic: 
    let traj_t := trajectory switched_example initial_point example_mode_solver in
      observable_trajectory = traj_t ->
      forall t n,
        0 < t <= 2 ->
        traj_t (t + INR (2 * n)%nat) = traj_t t. 
Proof.
    intros traj_t Hobservable.
    intros t n Ht.
    induction n.
    * simpl. rewrite Rplus_0_r. reflexivity.
    * rewrite Nat.mul_succ_r.
      rewrite plus_INR.
      (*hmmmm*)
      rewrite <- IHn.
      unfold traj_t.
      unfold switched_example.
      unfold trajectory.
      unfold switches.
      unfold switches_before.
      destruct Rle_lt_dec.
      - remember (INR (2 * n)) as inr_2n.
        remember (INR 2) as inr_2.
        pose proof pos_INR as H1.
        specialize (H1 2%nat).
        rewrite <- Heqinr_2 in H1.
        pose proof pos_INR as H2.
        specialize (H2 (2 * n)%nat).
        rewrite <- Heqinr_2n in H2.
        lra.
      - destruct Rle_lt_dec.
        * remember (INR (2 * n)) as inr_2n.
          pose proof pos_INR as H2.
          specialize (H2 (2 * n)%nat).
          rewrite <- Heqinr_2n in H2.
          lra.
        * rewrite (INR_IZR_INZ 2).
          rewrite <- Rplus_assoc.
          rewrite (floor1_plus_IZR _ (Z.of_nat 2)).
          rewrite Zabs2Nat.inj_add.
          rewrite Zabs2Nat.id.
          assert (H211: forall n, (n + 2)%nat = (n + 1 + 1)%nat). { lia. }
          rewrite H211.
          repeat rewrite Nat.add_1_r.
          repeat rewrite generate_switches_Sn.
          unfold example_mode_solver at 1.
          unfold example_mode_solver_implementation at 1.
          unfold controller at 1.
          destruct cond_positivity.
          * unfold traj_on_switches_helper at 1.
            unfold example_mode_solver at 1.
            unfold example_mode_solver_implementation at 1.
            unfold controller at 1.
            unfold dimension.
            destruct cond_positivity.
            * unfold mode2_solution.
Admitted. 
        
End SwitchedSystemExample.


