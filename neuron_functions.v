From Coq Require Import List Reals Lra Lia.

From Coquelicot Require Import Coquelicot.

From CoqE2EAI Require Import matrix_extensions piecewise_affine pwaf_operations.

Import ListNotations.
Import MatrixNotations.

Open Scope list_scope.
Open Scope scalar_scope.

Section LinearPiecewise.

Definition full_R_polyhedron (n: nat) := Polyhedron n nil.

Definition linear_body {n m: nat} (M: matrix (T:=R) m n) (b: colvec m): list _ :=
    cons (full_R_polyhedron n, (M, b)) nil.

Lemma linear_univalence {n m: nat} (M: matrix m n) (b: colvec m):
    pwaf_univalence (linear_body M b).
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b0 Ha Hb0 x Hintersect.
    destruct Ha. destruct Hb0.
    rewrite <- H. rewrite <- H0.
    reflexivity.
    contradiction H0. contradiction H.
Qed.

Definition LinearPWAF {in_dim out_dim: nat} (M: matrix out_dim in_dim) (b: colvec out_dim) := 
    mkPLF in_dim out_dim (linear_body M b) (linear_univalence M b).

Lemma linear_full_domain {n m: nat} (M: matrix m n) (b: colvec m):
    forall x, 
        in_pwaf_domain (LinearPWAF M b) x.
Proof.
    intros x.
    exists (full_R_polyhedron n, (M, b)).
    split.
    - simpl. left. reflexivity.
    - unfold full_R_polyhedron.
      simpl. contradiction.
Qed. 

End LinearPiecewise.

Section OutputPiecewise.

Definition OutputPWAF {in_dim out_dim: nat} :=
    LinearPWAF (mk_matrix out_dim in_dim Mone_seq) (null_vector out_dim).

End OutputPiecewise.

Section ReLUPiecewise.

(* Helper PWAF of zeroth dimension *)

Definition ZeroDim_polyhedron
    := Polyhedron 0 [Constraint 0 (null_vector 0) 0].

Theorem ZeroDim_polyhedron_full: 
    forall (x : colvec 0), in_convex_polyhedron x ZeroDim_polyhedron.
Proof.
   intros x.
   unfold in_convex_polyhedron.
   unfold ZeroDim_polyhedron.
   intros constraint HIn.
   destruct HIn; try contradiction.
   rewrite <- H.
   unfold satisfies_lc.
   rewrite dot_null_vector.
   lra. 
Qed.

Definition ZeroDim_body := 
    [(ZeroDim_polyhedron, (Mone (T:=R_Ring) (n:=0), null_vector 0))].

Theorem ZeroDim_univalence: 
    pwaf_univalence ZeroDim_body.
Proof.
   unfold pwaf_univalence.
   unfold ZeroDim_body.
   unfold ForallPairs.
   intros a b HaIn HbIn x HInboth.
   destruct HaIn; try contradiction.
   destruct HbIn; try contradiction.
   rewrite <- H. rewrite <- H0.
   simpl. reflexivity.
Qed.

Definition ZeroDimPWAF := mkPLF 0 0 ZeroDim_body ZeroDim_univalence.

Definition ReLU1d_polyhedra_left 
    := Polyhedron 1 [Constraint 1 Mone 0].
Definition ReLU1d_polyhedra_right 
    := Polyhedron 1 [Constraint 1 ((-1) * Mone)%scalar 0].

Lemma RelU1d_polyhedra_intersect:
    forall x, 
        in_convex_polyhedron x ReLU1d_polyhedra_left /\ 
        in_convex_polyhedron x ReLU1d_polyhedra_right ->
        dot Mone x = 0.
Proof.
    intros x Hintersect.
    unfold in_convex_polyhedron in Hintersect.
    destruct Hintersect.
    specialize (H (Constraint 1 Mone 0)). simpl in H. 
    specialize (H0 (Constraint 1 (scalar_mult (-1) Mone) 0)). simpl in H0.
    apply Rle_antisym.
    - apply H. auto.
    - rewrite <- Ropp_involutive.
      rewrite <- Ropp_0.
      apply Ropp_ge_le_contravar.
      apply Rle_ge. 
      apply Ropp_le_ge_contravar in H0. 
      rewrite dot_scalar_mult in H0. lra. 
      left. reflexivity.
Qed.  

Lemma x_is_0:
    forall (x: colvec 1),
        dot Mone x = 0 -> x = null_vector 1.
Proof.
    intros x Hdot.
    unfold null_vector.
    unfold mk_colvec.
    rewrite <- (mk_matrix_bij 0 x).
    unfold dot in Hdot.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    induction i. induction j.
    - rewrite <- Hdot at 2.
      unfold Mmult.
      rewrite coeff_mat_bij; try lia.
      compute. rewrite Rmult_1_l. rewrite Rplus_0_r.
      reflexivity.
    induction j.
    all: lia.
Qed.

Lemma RelU1d_polyhedra_intersect_0:
    forall x, 
        in_convex_polyhedron x ReLU1d_polyhedra_left /\ 
        in_convex_polyhedron x ReLU1d_polyhedra_right ->
        x = null_vector 1.
Proof.
    intros x Hintersect.
    apply x_is_0.
    apply RelU1d_polyhedra_intersect.
    apply Hintersect.
Qed.

Definition ReLU1d_body: list (ConvexPolyhedron 1 * (matrix (T:=R) 1 1 * colvec 1)) 
    := [(ReLU1d_polyhedra_left, (Mzero, null_vector 1));
        (ReLU1d_polyhedra_right, (Mone, null_vector 1))].

Definition ReLU1d_pwaf_univalence:
    pwaf_univalence ReLU1d_body.
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x Hintersect.
    unfold In in HaIn. simpl in HaIn.
    unfold In in HbIn. simpl in HbIn.
    destruct HaIn. destruct HbIn.
    - rewrite <- H. rewrite <- H0. simpl. reflexivity.
    destruct H0.
    - rewrite <- H. rewrite <- H0. simpl.
      rewrite <-H in Hintersect. rewrite <- H0 in Hintersect.
      pose proof RelU1d_polyhedra_intersect_0 as Hxzero.
      specialize (Hxzero x Hintersect).
      rewrite Mmult_Mzero.
      rewrite Hxzero.
      rewrite Mmult_one_l.
      rewrite Mplus_comm.
      rewrite Mplus_zero_r.
      rewrite Mplus_null_vector.
      reflexivity. 
    contradiction. destruct H. destruct HbIn.
    - rewrite <- H. rewrite <- H0. simpl.
      rewrite <-H in Hintersect. rewrite <- H0 in Hintersect.
      pose proof RelU1d_polyhedra_intersect_0 as Hxzero.
      specialize (Hxzero x).
      rewrite Mmult_Mzero.
      rewrite Hxzero.
      rewrite Mmult_one_l.
      rewrite Mplus_null_vector.
      rewrite Mplus_comm.
      rewrite Mplus_zero_r.
      reflexivity.
      split; apply Hintersect.
    destruct H0.
    - rewrite <- H. rewrite <- H0. simpl. reflexivity.
    contradiction. contradiction.
Qed.
      
Definition ReLU1dPWAF := mkPLF 1 1 ReLU1d_body ReLU1d_pwaf_univalence.

Fixpoint ReLU_PWAF_helper (in_dim: nat): PWAF in_dim in_dim :=
    match in_dim with
    | 0 => ZeroDimPWAF
    | S n => pwaf_concat ReLU1dPWAF (ReLU_PWAF_helper n)
    end.

Definition ReLU_PWAF {in_dim out_dim: nat}: PWAF in_dim out_dim :=
    pwaf_compose OutputPWAF (ReLU_PWAF_helper in_dim).

Definition ReLU_plain {n: nat} (x: colvec n): colvec n :=
    mk_colvec n (
        fun i =>
            let input_i := coeff_colvec 0 x i in
            if Rle_dec input_i 0 then 0 else input_i 
    ).

End ReLUPiecewise.
