From Coq Require Import Nat Reals List Arith Lia Lra.
From Coquelicot Require Import Coquelicot.

Import ListNotations.

Section StandardLibraryLemmas.

Lemma nat_pred_le_lt:
    forall n m, (n <= Nat.pred m)%nat -> (m >= 1)%nat -> (n < m)%nat.
Proof.
    intros n m Hn Hn_ge_1.
    compute.
    induction m.
    - simpl in Hn.
      apply le_n_S in Hn.
      apply (Nat.le_trans (S n) 1).
      apply Hn. apply Hn_ge_1.
    - rewrite Nat.pred_succ in Hn.
      apply le_n_S.
      apply Hn.
Qed.

Lemma f_equal2_plus_R:
    forall x1 y1 x2 y2 : R,
    x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2.
Proof.
    intros x1 y1 x2 y2.
    lra.
Qed.

Lemma list_prod_empty:
    forall A B l,
        list_prod (A:=A) (B:=B) l [] = [].
Proof.
    intros A B l.
    induction l.
    * compute. reflexivity.
    * unfold list_prod.
      simpl. apply IHl.
Qed.

End StandardLibraryLemmas.

Section CoquelicotGeneralLemmas.

Lemma coeff_Tn_default:
    forall n T (it: Tn n T) d i,
        (i >= n)%nat ->
        coeff_Tn d it i = d.
Proof.
    intros n T it d.
    induction n. reflexivity.
    intros i Hi.
    unfold coeff_Tn.
    assert (Hi2: i = S (pred i)). {
        apply S_pred_pos. lia.
    }
    rewrite Hi2.
    induction it.
    fold (coeff_Tn (T:=T) (n:=n)). simpl.
    specialize (IHn b (pred i)).
    apply IHn.
    lia.
Qed.

Lemma zero_is_0:
    zero = 0.
Proof.
    reflexivity.
Qed.

Lemma sum_n_m_shift:
    forall (f: nat -> R) n m shift,
    sum_n_m f n m = sum_n_m (fun l => f (l - shift)%nat) (n + shift) (m + shift).
Proof.
    intros f n m shift.
    induction shift.
    * repeat rewrite Nat.add_0_r.
      apply sum_n_m_ext.
      intros n0.
      rewrite Nat.sub_0_r.
      reflexivity.
    * repeat rewrite Nat.add_succ_r.
      rewrite <- sum_n_m_S.
      apply IHshift.
Qed.

Lemma floor1_tech:
    forall r n,
       IZR n < r -> r <= IZR n + 1 -> floor1 r = n.
Proof.
    intros r n H1 H2.
    unfold floor1.
    destruct floor1_ex as [x Hx]. simpl.
    apply Z.le_antisymm.
    - apply Zlt_succ_le. simpl.
      apply lt_IZR.
      apply (Rlt_le_trans _ r).
      * destruct Hx as [H H0].
        apply H.
      * destruct Hx as [H H0].
        rewrite succ_IZR.
        apply H2.
    - apply Zlt_succ_le.
      apply lt_IZR.
      rewrite succ_IZR.
      apply (Rlt_le_trans _ r).
      * apply H1.
      * destruct Hx as [H H0].
        apply H0.
Qed. 

Lemma floor1_plus_IZR:
    forall r n,
        floor1 (r + IZR n) = (floor1 r + n)%Z.
Proof.
    intros r n.
    apply floor1_tech.
    * rewrite plus_IZR.
      apply Rplus_lt_compat_r.
      unfold floor1.
      destruct floor1_ex.
      simpl.
      apply a.
    * rewrite plus_IZR.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (IZR n) 1).
      rewrite <- Rplus_assoc.
      apply Rplus_le_compat_r.
      unfold floor1. destruct floor1_ex. simpl.
      destruct a. apply H0.
Qed.
          
End CoquelicotGeneralLemmas.

(*---------------------------------------------------------------------------*)

Section CoquelicotMatrix.

Lemma coeff_mat_default:
    forall A d m n (M: matrix (T:=A) m n) i j,
        ((i >= m)%nat \/ (j >= n)%nat) ->
        coeff_mat d M i j = d.
Proof.
    intros A d m n M i j Hij.
    destruct Hij as [Hi|Hj].
    - unfold coeff_mat. 
      rewrite (coeff_Tn_default _ _ _ _ i); try lia.
      destruct (lt_dec j n).
      * apply coeff_Tn_bij; try lia.
      * rewrite coeff_Tn_default; try lia. reflexivity.
    - unfold coeff_mat. rewrite coeff_Tn_default; try lia. reflexivity. 
Qed.

Definition transpose {m n: nat} (M: matrix m n) :=
    mk_matrix n m (fun i j => coeff_mat 0 M j i).

Theorem transpose_transpose:
    forall m n (M: matrix m n),
    transpose (transpose M) = M.
Proof.
    intros m n M.
    unfold transpose.
    unfold transpose.
    rewrite <- (mk_matrix_bij 0).
    apply mk_matrix_ext.
    intros i j Hi Hj.
    repeat (rewrite coeff_mat_bij; try lia).
    reflexivity.
Qed.  

Theorem Mmult_Mzero: 
    forall n m (M: matrix (T:=R) m n), Mmult (n:=m) Mzero M = (Mzero (n:=n)).
Proof.
    intros n m M.
    unfold Mmult.
    unfold Mzero.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    unfold sum_n.
    rewrite <- (sum_n_m_const_zero 0 (Init.Nat.pred m)) at 1.
    apply sum_n_m_ext_loc.
    intros k Hk.
    rewrite coeff_mat_bij; try lia.
    rewrite Rmult_0_l.
    reflexivity.
Qed.

Definition scalar_mult {m n: nat} (c:R) (v: matrix m n) :=
    mk_matrix m n (fun i j => c * coeff_mat 0 v i j).

End CoquelicotMatrix.

(*---------------------------------------------------------------------------*)

(** * Theory of column vectors

Basic theory of column vectors, wrapper for Coquelicot matricies

Operations:
- Contruction via mk_colvec
- Coefficients retrieval via coeff_colvec
- Special cases: dimesion zero vectors, null vectors
- Conversions to n*1 and 1*n matricies
- Dot product
*)

Section ColumnVectors.

(* Column vector is a 1d matrix *)
Definition colvec m := matrix (T:=R) m 1.

(* There is only a single colvec of dimension zero *)
Lemma unique_colvec_0:
    forall (v1: colvec 0) (v2: colvec 0),
        v1 = v2.
Proof.
    intros v1 v2.
    rewrite <- (mk_matrix_bij 0 v1).
    rewrite <- (mk_matrix_bij 0 v2).
    apply mk_matrix_ext.
    intros i j Hi Hj.
    rewrite coeff_mat_default; try lia.
Qed.

(* Coeficient of a colvec V[i] with x0 as default value*)
Definition coeff_colvec {m: nat} (x0: R) (V:colvec m) (i:nat) :=
  coeff_mat x0 V i 0.

(* Construction of a colvec *)
Definition mk_colvec m (f: nat -> R) : colvec m := 
    mk_matrix m 1 (fun i j => (f i)).

(* Dot product *)
Definition dot {n:nat} (c1: colvec n) (c2: colvec n) : R :=
    coeff_mat 0 (Mmult (transpose c1) c2) 0 0.

(* Null vector *)
Definition null_vector m := mk_colvec m (fun i => 0).

(* Associativity of multiplication with constant and dot product *)
Theorem dot_scalar_mult:
    forall dim c (v1: colvec dim) (v2: colvec dim),
    dot (scalar_mult c v1) v2 = Rmult c (dot v1 v2).
Proof.
    intros dim c v1 v2.
    unfold dot.
    unfold Mmult.
    repeat rewrite (coeff_mat_bij _ _ 0 0 Nat.lt_0_1 Nat.lt_0_1).
    rewrite <- (sum_n_mult_l c).
    apply sum_n_ext_loc.
    intros n Hloc.
    induction dim.
    * compute. lra.
    * assert (Hdim: (S dim >= 1)%nat). lia.
      pose proof (nat_pred_le_lt n (S dim) Hloc Hdim) as Hndim.
      unfold scalar_mult.
      unfold transpose.
      rewrite (coeff_mat_bij _ _ 0 n Nat.lt_0_1 Hndim).
      unfold mk_colvec.
      rewrite (coeff_mat_bij _ _ 0 n Nat.lt_0_1 Hndim).
      unfold coeff_colvec.
      rewrite (coeff_mat_bij _ _ n 0 Hndim Nat.lt_0_1).
      rewrite Rmult_assoc.
      reflexivity.
Qed.

(* 0 dot v1 = 0 *)
Theorem dot_null_vector:
    forall dim x, dot (null_vector dim) x = 0.
Proof.
    intros dim x.
    unfold dot.
    unfold Mmult.
    rewrite (coeff_mat_bij _ _ 0 0 Nat.lt_0_1 Nat.lt_0_1).
    unfold sum_n.
    unfold coeff_colvec.
    unfold null_vector.
    unfold mk_colvec.
    rewrite <- zero_is_0.
    rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 (Nat.pred dim)) at 1.
    apply sum_n_m_ext_loc.
    intros n Hn.
    destruct Hn.
    induction dim.
    * compute. lra.
    * assert (Hdim: (S dim >= 1)%nat). lia. 
      pose proof (nat_pred_le_lt n (S dim) H0 Hdim) as Hndim.
      unfold transpose.
      rewrite (coeff_mat_bij _ _ 0 n Nat.lt_0_1 Hndim). 
      rewrite (coeff_mat_bij _ _ n 0 Hndim Nat.lt_0_1).
      rewrite Rmult_0_l.
      reflexivity.
Qed.

(* v1 + 0 = v1 *)
Theorem Mplus_null_vector: 
    forall dim v, Mplus v (null_vector dim) = v.
Proof. 
    intros dim v.
    unfold Mplus. unfold colvec in v. unfold null_vector. unfold mk_colvec.
    rewrite <- (mk_matrix_bij 0 v) at 1.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    unfold coeff_colvec.
    rewrite (coeff_mat_bij 0 (fun _ _ => 0) i j).
    rewrite Rplus_0_r. 
    induction j. reflexivity. lia.
    apply Hi. lia. 
Qed.

(* For a matrix M and a vector v, M*v can be split into multiple
   dot products over matrix rows *)
Theorem Mmult_dot_split:
    forall n m M v, Mmult M v = mk_colvec n (
        fun i => 
            dot (mk_colvec m (fun j => coeff_mat 0 M i j)) v
    ).
Proof.
    intros n m M V.
    unfold Mmult. 
    unfold mk_colvec. unfold dot. unfold Mmult. 
    apply mk_matrix_ext.
    intros i j Hi Hj.
    rewrite coeff_mat_bij.
    apply sum_n_ext_loc.
    intros n0 Hn0.
    induction m.
    * compute. lra.
    * unfold transpose.
      rewrite coeff_mat_bij.
      unfold coeff_colvec.
      rewrite coeff_mat_bij.
      induction j. reflexivity. lia.
      apply nat_pred_le_lt. apply Hn0. lia. lia. lia.
      apply nat_pred_le_lt. apply Hn0. lia. lia. lia.
Qed.

(* v1 * (v2 + v3) = v1 * v2 + v1 * v3 *)
Theorem dot_Mplus_distr:
    forall dim (v1: colvec dim) v2 v3,
        dot v1 (Mplus v2 v3) = (dot v1 v2) + (dot v1 v3).
Proof.
    intros dim v1 v2 c3.
    unfold dot.
    unfold Mplus.
    unfold Mmult.
    repeat (rewrite coeff_mat_bij; try lia).
    assert (Hplus: forall a b, a + b = plus a b). { reflexivity. }
    rewrite Hplus.
    rewrite <- sum_n_plus.
    apply sum_n_ext_loc.
    intros n Hn.
    unfold mk_colvec. unfold coeff_colvec.
    induction dim.
    * compute. lra.
    * repeat (rewrite coeff_mat_bij; try lia).
      rewrite Rmult_plus_distr_l. reflexivity.
Qed. 

(* Associativity of dot and matrix multiplication via transposition.
   For matrix M and vectors v1 v2: v1 * (M * v2) = (v1^T * M)^T * v2 *)
Theorem dot_Mmult:
    forall m n v1 (M: matrix m n) v2,
        dot v1 (Mmult M v2) = dot (transpose (Mmult (transpose v1) M)) v2.
Proof.
    intros m n v1 M v2.
    unfold dot.
    repeat rewrite colvec2matrix_spec.
    rewrite Mmult_assoc.
    rewrite transpose_transpose.
    reflexivity.
Qed.    

End ColumnVectors.

(*---------------------------------------------------------------------------*)

Section ReshapeOperations.

Definition block_diag_matrix 
    {in_dim1 in_dim2 out_dim1 out_dim2: nat}  
    (M1: matrix (T:=R) out_dim1 in_dim1)
    (M2: matrix (T:=R) out_dim2 in_dim2): 
    matrix (out_dim1 + out_dim2) (in_dim1 + in_dim2) :=
    mk_matrix (out_dim1 + out_dim2) (in_dim1 + in_dim2) 
        (fun i j => 
            if (ltb i out_dim1) then 
                (if (ltb j in_dim1) then
                    coeff_mat 0 M1 i j
                else
                    0)
            else 
                (if (ltb j in_dim1) then
                    0
                else 
                    coeff_mat 0 M2 (i - out_dim1) (j - in_dim1))
        ).

Definition extend_colvec_at_bottom {n: nat} (v: colvec n) (new_dim: nat) :=
    mk_colvec new_dim (
        fun i =>
        match i <? n with
        | true => coeff_colvec 0 v i
        | false => 0
        end 
    ).

Lemma extend_colvec_at_bottom_same_dim:
    forall d (v: colvec d),
        extend_colvec_at_bottom v d = v.
Proof.
    intros d v.
    unfold colvec in v.
    unfold extend_colvec_at_bottom.
    rewrite <- (mk_matrix_bij 0 v) at 1.
    unfold mk_colvec.
    destruct d.
    * apply unique_colvec_0.
    * apply mk_matrix_ext.
      intros i j Hi Hj.
      rewrite <- Nat.ltb_lt in Hi.
      rewrite Hi.
      unfold coeff_colvec.
      induction j.
      - reflexivity.
      - lia.
Qed.

Lemma extend_colvec_at_bottom_preserves_equality:
    forall d1 d2 (v1: colvec d1) v2,
      v1 = v2 <->
      extend_colvec_at_bottom v1 (d1 + d2) = extend_colvec_at_bottom v2 (d1 + d2).
Proof.  
    intros d1 d2 v1 v2.
    rewrite <- (mk_matrix_bij 0 v1).
    rewrite <- (mk_matrix_bij 0 v2).
    split.
    {
      intros Hequal.
      unfold colvec in v1. unfold colvec in v2.
      unfold extend_colvec_at_bottom.
      unfold mk_colvec.
      apply mk_matrix_ext.
      intros i j Hi Hj.
      remember (i <? d1) as r.
      destruct r; try reflexivity.
      symmetry in Heqr. rewrite Nat.ltb_lt in Heqr.
      pose proof (mk_matrix_ext (T:=R)) as Hext.
      specialize (Hext d1 1%nat (coeff_mat 0 v1) (coeff_mat 0 v2)).
      unfold coeff_colvec.
      repeat (rewrite coeff_mat_bij; try lia).
      apply Hext; try lia.
      apply Hequal.
    }
    {
      intros Hequal.
      apply mk_matrix_ext.
      intros i j Hi Hj.
      unfold extend_colvec_at_bottom in Hequal.
      unfold mk_colvec in Hequal.
      pose proof (mk_matrix_ext (T:=R)) as Hext.
      specialize (Hext (d1 + d2)%nat 1%nat).
      specialize (Hext (fun i _ : nat => 
                          if i <? d1 then 
                            coeff_colvec 0 (mk_matrix d1 1 (coeff_mat 0 v1)) i
                          else 
                            0)).
      specialize (Hext (fun i _ : nat => 
                          if i <? d1 then 
                            coeff_colvec 0 (mk_matrix d1 1 (coeff_mat 0 v2)) i
                          else 
                            0)).
      destruct Hext as [Hext1 Hext2].               
      specialize (Hext2 Hequal).
      specialize (Hext2 i j).
      pose proof Hi as Hi_cp.
      rewrite <- Nat.ltb_lt in Hi.
      rewrite Hi in Hext2.
      unfold coeff_colvec in Hext2.
      repeat (rewrite coeff_mat_bij in Hext2; try lia).
      induction j.
      * apply Hext2; try lia.
      * lia.
    }
Qed.

Definition extend_colvec_on_top {n: nat} (v: colvec n) (new_dim: nat) :=
    mk_colvec new_dim (
        fun i => 
        match i <? (new_dim - n) with
        | true => 0
        | false => coeff_colvec 0 v (i - (new_dim - n))
        end
    ).

Lemma extend_colvec_on_top_same_dim:
    forall d (v: colvec d),
      extend_colvec_on_top v d = v.    
Proof.
    intros d v.
    unfold colvec in v.
    unfold extend_colvec_on_top.
    rewrite <- (mk_matrix_bij 0 v) at 1.
    unfold mk_colvec.
    destruct d.
    * apply unique_colvec_0.
    * apply mk_matrix_ext.
      intros i j Hi Hj.
      rewrite Nat.sub_diag. 
      simpl.
      unfold coeff_colvec.
      rewrite Nat.sub_0_r.
      induction j.
      - reflexivity.
      - lia.
Qed.    

Lemma extend_colvec_on_top_preserves_equality:
    forall d1 d2 (v1: colvec d2) v2,
      v1 = v2 <->
      extend_colvec_on_top v1 (d1 + d2) = extend_colvec_on_top v2 (d1 + d2).
Proof.  
    intros d1 d2 v1 v2.
    rewrite <- (mk_matrix_bij 0 v1).
    rewrite <- (mk_matrix_bij 0 v2).
    split.
    {
      intros Hequal.
      unfold colvec in v1. unfold colvec in v2.
      unfold extend_colvec_on_top.
      unfold mk_colvec.
      apply mk_matrix_ext.
      intros i j Hi Hj.
      rewrite Nat.add_sub.
      remember (i <? d1) as r.
      destruct r; try reflexivity.
      symmetry in Heqr. rewrite Nat.ltb_ge in Heqr.
      pose proof (mk_matrix_ext (T:=R)) as Hext.
      specialize (Hext d2 1%nat (coeff_mat 0 v1) (coeff_mat 0 v2)).
      unfold coeff_colvec.
      repeat (rewrite coeff_mat_bij; try lia).
      apply Hext; try lia.
      apply Hequal.
    }
    {
      intros Hequal.
      apply mk_matrix_ext.
      intros i j Hi Hj.
      unfold extend_colvec_on_top in Hequal.
      unfold mk_colvec in Hequal.
      rewrite Nat.add_sub in Hequal.
      pose proof (mk_matrix_ext (T:=R)) as Hext.
      specialize (Hext (d1 + d2)%nat 1%nat).
      specialize (Hext (fun i _ : nat => 
                          if i <? d1 then 
                            0
                          else 
                            coeff_colvec 0 (mk_matrix d2 1 (coeff_mat 0 v1)) (i - d1))).
      specialize (Hext (fun i _ : nat => 
                          if i <? d1 then 
                            0
                          else 
                            coeff_colvec 0 (mk_matrix d2 1 (coeff_mat 0 v2)) (i - d1))).
      destruct Hext as [Hext1 Hext2].               
      specialize (Hext2 Hequal).
      specialize (Hext2 (i + d1)%nat j).
      assert (Hi2: (d1 <= i + d1)%nat). lia.
      rewrite <- Nat.ltb_ge in Hi2.
      rewrite Hi2 in Hext2.
      rewrite Nat.add_sub in Hext2.
      unfold coeff_colvec in Hext2.
      repeat (rewrite coeff_mat_bij in Hext2; try lia).
      induction j.
      * apply Hext2; try lia.
      * lia.
    }
Qed.

Definition colvec_concat {n m: nat} (v1: colvec n) (v2: colvec m) :=
    Mplus (extend_colvec_at_bottom v1 (n + m)) (extend_colvec_on_top v2 (n + m)).

Lemma dot_extend_at_bottom:
    forall d1 d2 (v: colvec d1) x1 x2,
        dot (extend_colvec_at_bottom v (d1 + d2)) (colvec_concat x1 x2) =
        dot v x1.
Proof.
    intros d1 d2 v x1 x2.
    destruct d1.
    * destruct d2.
      - rewrite (unique_colvec_0 (extend_colvec_at_bottom v (0 + 0)) v).
        rewrite (unique_colvec_0 (colvec_concat x1 x2) x1).
        reflexivity.
      - unfold dot.
        unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite sum_O.
        rewrite coeff_mat_default; try lia.
        rewrite Rmult_0_l. rewrite Nat.add_0_l at 1.
        rewrite <- zero_is_0.
        rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 (d2)).
        apply sum_n_ext_loc.
        intros n Hn.
        unfold transpose.
        unfold extend_colvec_at_bottom.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        simpl.
        apply Rmult_0_l.
    * destruct d2.
      - unfold dot.
        unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_0_r at 1.
        apply sum_n_ext_loc.
        intros n Hn.
        unfold transpose.
        unfold extend_colvec_at_bottom. unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        simpl in Hn.
        unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        apply le_lt_n_Sm in Hn.
        rewrite <- Nat.ltb_lt in Hn.
        rewrite Hn.
        unfold coeff_colvec.
        rewrite Rplus_0_r.
        reflexivity.
      - unfold extend_colvec_at_bottom.
        unfold colvec_concat.
        unfold dot. unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        unfold sum_n. simpl.
        rewrite <- (Rplus_0_r (sum_n_m _ 0 (d1))).
        rewrite (sum_n_m_Chasles _ _ d1 (d1 + S d2)); try lia.
        apply f_equal2_plus_R.
        * apply sum_n_ext_loc.
          intros n Hn.
          unfold transpose.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          rewrite <- Nat.add_succ_l.
          rewrite Nat.add_sub.
          apply le_lt_n_Sm in Hn.
          rewrite <- Nat.ltb_lt in Hn.
          rewrite Hn.
          unfold coeff_colvec.
          rewrite Rplus_0_r.
          reflexivity.
        * simpl.
          rewrite <- zero_is_0.
          rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) (S d1) (d1 + S d2)) at 1.
          apply sum_n_m_ext_loc.
          intros k Hk.
          unfold transpose.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          destruct Hk.
          rewrite <- Nat.ltb_ge in H.
          rewrite H.
          rewrite Rmult_0_l.
          reflexivity.
Qed.

Lemma dot_extend_on_top:
    forall d1 d2 (v: colvec d2) x1 x2,
        dot (extend_colvec_on_top v (d1 + d2)) (colvec_concat x1 x2) =
        dot v x2.
Proof.
    intros d1 d2 v x1 x2.
    destruct d1.
    * destruct d2.
      - rewrite (unique_colvec_0 (extend_colvec_on_top v (0 + 0)) v).
        rewrite (unique_colvec_0 (colvec_concat x1 x2) x1).
        reflexivity.
      - unfold dot.
        unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_0_l at 1.
        apply sum_n_ext_loc.
        intros n Hn.
        unfold transpose.
        unfold extend_colvec_at_bottom. unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        simpl in Hn.
        unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub. simpl.
        unfold coeff_colvec.
        rewrite Rplus_0_l.
        rewrite Nat.sub_0_r.
        reflexivity.
    * destruct d2.
      - unfold dot.
        unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite sum_O.
        rewrite coeff_mat_default; try lia.
        rewrite Rmult_0_l. rewrite Nat.add_0_r at 1.
        rewrite <- zero_is_0.
        rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 (d1)).
        apply sum_n_ext_loc.
        intros n Hn.
        unfold transpose.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        apply le_lt_n_Sm in Hn.
        rewrite <- Nat.ltb_lt in Hn.
        rewrite Hn.
        apply Rmult_0_l.
      - unfold extend_colvec_on_top.
        unfold colvec_concat.
        unfold dot. unfold Mmult.
        repeat (rewrite coeff_mat_bij; try lia).
        unfold sum_n. simpl.
        rewrite <- (Rplus_0_l (sum_n_m _ 0 (d2))).
        rewrite (sum_n_m_Chasles _ _ d1 (d1 + S d2)); try lia.
        apply f_equal2_plus_R.
        * simpl.
          rewrite <- zero_is_0.
          rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 d1) at 1.
          apply sum_n_m_ext_loc.
          intros k Hk.
          unfold transpose.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          simpl.
          rewrite Nat.add_succ_r.
          rewrite <- Nat.add_succ_l.
          rewrite Nat.add_sub.
          destruct Hk.
          apply le_lt_n_Sm in H0.
          rewrite <- Nat.ltb_lt in H0.
          rewrite H0.
          rewrite Rmult_0_l.
          reflexivity.
        * rewrite (sum_n_m_shift _ 0 d2 (S d1)).
          rewrite Nat.add_0_l.
          rewrite Nat.add_succ_r at 1.
          rewrite (Nat.add_succ_r d2 d1).
          rewrite (Nat.add_comm d1 d2).
          apply sum_n_m_ext_loc.
          intros n Hn.
          unfold transpose.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          rewrite Nat.add_succ_r at 1.
          do 2 rewrite <- Nat.add_succ_l.
          do 2 rewrite Nat.add_sub.
          destruct Hn.
          rewrite <- Nat.ltb_ge in H.
          rewrite H.
          unfold coeff_colvec.
          rewrite Nat.add_succ_r.
          rewrite <- Nat.add_succ_l.
          rewrite Nat.add_sub.
          rewrite Rplus_0_l.
          reflexivity.
Qed.

Lemma colvec_concat_eq:
    forall d1 d2 (v1: colvec d1) (v2: colvec d2) v3 v4,
        v1 = v3 -> v2 = v4 ->
        colvec_concat v1 v2 = colvec_concat v3 v4.
Proof.
    intros d1 d2 v1 v2 v3 v4 Hv13 Hv24.
    unfold colvec_concat.
    rewrite Hv13. rewrite Hv24.
    reflexivity.
Qed.

Lemma Mplus_colvec_concat:
    forall d1 d2 (v1: colvec d1) (v2: colvec d2) v3 v4,
        Mplus (colvec_concat v1 v2) (colvec_concat v3 v4) =
        colvec_concat (Mplus v1 v3) (Mplus v2 v4).
Proof.
    intros d1 d2 v1 v2 v3 v4.
    unfold colvec_concat.
    rewrite (Mplus_assoc _ (extend_colvec_at_bottom v3 _) _).
    rewrite <- (Mplus_assoc (extend_colvec_at_bottom v1 _) _ _).
    rewrite (Mplus_comm (extend_colvec_on_top v2 _) (extend_colvec_at_bottom v3 _)).
    rewrite (Mplus_assoc (extend_colvec_at_bottom v1 _) _ _).
    rewrite <- (Mplus_assoc _ (extend_colvec_on_top v2 _) _).
    unfold Mplus.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    destruct d1.
    - destruct d2.
      * lia.
      * unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec. unfold coeff_colvec.
        do 7 (rewrite coeff_mat_bij; try lia).
        simpl. rewrite Nat.sub_diag. simpl.
        repeat rewrite Rplus_0_l.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.sub_0_r.
        reflexivity.
    - destruct d2.
      * unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec. unfold coeff_colvec.
        do 9 (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub. 
        rewrite Nat.add_0_r in Hi.
        rewrite <- Nat.ltb_lt in Hi.
        rewrite Hi. rewrite Rplus_0_l. reflexivity.
      * unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec. unfold coeff_colvec.
        do 7 (rewrite coeff_mat_bij; try lia).
        rewrite (coeff_mat_bij (m:=(S d1 + S d2))); try lia.
        rewrite Nat.add_sub.
        remember (i <? S d1) as r.
        destruct r.
        - repeat rewrite Rplus_0_r.
          symmetry in Heqr. rewrite Nat.ltb_lt in Heqr.
          rewrite coeff_mat_bij; try lia.
          reflexivity.
        - repeat rewrite Rplus_0_l.
          symmetry in Heqr. rewrite Nat.ltb_ge in Heqr. 
          rewrite coeff_mat_bij; try lia.
          reflexivity.
Qed.   

Lemma MMmult_block_diag_matrix:
    forall m1 n1 m2 n2 (A1: matrix m1 n1) (A2: matrix m2 n2)
        (v1: colvec n1) (v2: colvec n2),
        Mmult (block_diag_matrix A1 A2) (colvec_concat v1 v2) = 
        colvec_concat (Mmult A1 v1) (Mmult A2 v2).
Proof.
    intros m1 n1 m2 n2 A1 A2 v1 v2.
    unfold colvec_concat.
    rewrite (Mmult_distr_l (block_diag_matrix A1 A2) _ _).
    unfold Mplus.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    induction j; try lia.
    destruct (lt_dec i m1) as [Hile|Helt].
    - destruct m1. lia. simpl in Hile.
      assert (H1: coeff_mat zero 
        (Mmult (block_diag_matrix A1 A2) (extend_colvec_on_top v2 _)) i 0 = 0). { 
        unfold Mmult.
        rewrite coeff_mat_bij; try lia.
        unfold sum_n.
        rewrite <- zero_is_0.
        rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 (pred (n1 + n2))).
        destruct (le_gt_dec (n1 + n2) 0).
        - apply le_n_0_eq in l.
          repeat rewrite <- l at 1. simpl. 
          repeat rewrite sum_n_n.
          rewrite (coeff_mat_default _ _ _ _ _ 0 0); try lia.
          apply Rmult_0_r.
        - apply sum_n_m_ext_loc.
          intros n Hn.
          unfold extend_colvec_on_top.
          unfold mk_colvec. unfold coeff_colvec.
          rewrite coeff_mat_bij; try lia.
          rewrite Nat.add_sub.
          remember (n <? n1) as r.
          induction r.
          * apply Rmult_0_r.
          * unfold block_diag_matrix.
            rewrite coeff_mat_bij; try lia.
            apply Nat.ltb_lt in Hile.
            rewrite Hile. rewrite <- Heqr.
            apply Rmult_0_l.
      }
      rewrite H1. rewrite Rplus_0_r.
      assert (H2: coeff_mat zero (
        extend_colvec_on_top (Mmult A2 v2) (S m1 + m2)) i 0 = 0). {
        unfold extend_colvec_on_top. unfold mk_colvec.
        rewrite coeff_mat_bij; try lia.
        rewrite Nat.add_sub.
        apply Nat.ltb_lt in Hile.
        rewrite Hile. reflexivity.
      }
      rewrite H2. rewrite Rplus_0_r.
      unfold Mmult at 1. 
      repeat rewrite coeff_mat_bij; try lia.
      unfold sum_n. rewrite (sum_n_m_Chasles _ _ (pred n1) _); try lia.
      rewrite <- (Rplus_0_r (coeff_mat zero 
        (extend_colvec_at_bottom (Mmult A1 v1) (S m1 + m2)) i 0)).
      apply f_equal2_plus_R.
      * unfold extend_colvec_at_bottom.
        unfold mk_colvec. unfold coeff_colvec.
        rewrite coeff_mat_bij; try lia.
        rewrite <- Nat.ltb_lt in Hile. rewrite Hile.
        unfold Mmult. rewrite Nat.ltb_lt in Hile.
        rewrite coeff_mat_bij; try lia.
        unfold sum_n. apply sum_n_m_ext_loc.
        intros k Hk.
        induction n1.
        * simpl in Hk.
          destruct Hk as [Hk1 Hk2].
          apply le_n_0_eq in Hk2.
          rewrite <- Hk2. simpl.
          induction n2.
          * rewrite coeff_mat_default; try lia.
            rewrite (coeff_mat_default _ _ _ _ v1); try lia.
            rewrite Rmult_0_l. rewrite Rmult_0_r. reflexivity.
          * rewrite coeff_mat_bij; try lia.
            rewrite (coeff_mat_default _ _ _ _ v1); try lia.
            repeat rewrite Rmult_0_r. reflexivity.
        * rewrite coeff_mat_bij; try lia.
          unfold block_diag_matrix.
          rewrite coeff_mat_bij; try lia.
          rewrite <- Nat.ltb_lt in Hile. rewrite Hile.
          remember (k <? S n1) as r.
          induction r.
          - reflexivity.
          - symmetry in Heqr. rewrite Nat.ltb_ge in Heqr. lia.
      * unfold extend_colvec_at_bottom.
        unfold mk_colvec. unfold coeff_colvec.
        rewrite <- zero_is_0.
        rewrite <- (sum_n_m_const_zero 
            (G:=R_AbelianGroup) (S (pred n1)) (pred (n1 + n2))).
        apply sum_n_m_ext_loc.
        intros k Hk.
        rewrite coeff_mat_bij; try lia.
        rewrite sum_n_m_const_zero.
        destruct Hk.
        remember (k <? n1) as r.
        induction r.
        * symmetry in Heqr. rewrite Nat.ltb_lt in Heqr. lia.
        * apply Rmult_0_r.  
    - apply not_lt in Helt.
      assert (Hib: i <? m1 = false). {
         rewrite Nat.ltb_ge.
         lia.
      }
      apply f_equal2_plus_R.
      * assert (H1: coeff_mat zero 
        (Mmult (block_diag_matrix A1 A2) (extend_colvec_at_bottom v1 _)) i 0 = 0). 
        { 
            unfold Mmult.
            rewrite coeff_mat_bij; try lia.
            unfold sum_n.
            rewrite <- zero_is_0.
            rewrite <- (sum_n_m_const_zero (G:=R_AbelianGroup) 0 (pred (n1 + n2))).
            apply sum_n_m_ext_loc.
            intros n Hn.
            destruct (le_gt_dec (n1 + n2) 0).
            - apply le_n_0_eq in l.
              rewrite (coeff_mat_default _ _ _ _ _ n 0); try lia.
              apply Rmult_0_r.
            - unfold extend_colvec_at_bottom.
              unfold mk_colvec. unfold coeff_colvec.
              rewrite coeff_mat_bij; try lia.
              unfold block_diag_matrix.
              rewrite coeff_mat_bij; try lia.
              rewrite Hib.
              destruct (n <? n1).
              - apply Rmult_0_l.
              - apply Rmult_0_r.
        }
        rewrite H1.
        assert (H2: coeff_mat zero (
            extend_colvec_at_bottom (Mmult A1 v1) (m1 + m2)) i 0 = 0). {
            unfold extend_colvec_at_bottom. unfold mk_colvec.
            rewrite coeff_mat_bij; try lia.
            rewrite Hib.
            reflexivity.
        }
        rewrite H2.
        reflexivity.
      * unfold extend_colvec_on_top. unfold block_diag_matrix.
        unfold Mmult. unfold mk_colvec. unfold coeff_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        repeat rewrite Nat.add_sub.
        rewrite Hib.
        destruct n1.
        * destruct n2.
          * repeat rewrite sum_n_n.
            repeat rewrite coeff_mat_default; try lia.
            reflexivity.
          * apply sum_n_ext_loc.
            intros n Hn. simpl.
            repeat rewrite coeff_mat_bij; try lia.
            rewrite Hib. rewrite <- zero_is_0.
            rewrite Nat.sub_0_r. reflexivity.
        * rewrite <- (Rplus_0_l (sum_n _ (pred n2))).
          unfold sum_n. 
          rewrite (sum_n_m_Chasles _ _ (pred (S n1)) _); try lia.
          apply f_equal2_plus_R.
          - rewrite <- zero_is_0.
            rewrite <- (sum_n_m_const_zero 
              (G:=R_AbelianGroup) 0 (pred (S n1))).
            apply sum_n_m_ext_loc.
            intros k Hk.
            rewrite coeff_mat_bij; try lia.
            rewrite Hib.
            destruct Hk.
            simpl in H0.
            apply le_lt_n_Sm in H0.
            rewrite <- Nat.ltb_lt in H0.
            rewrite H0.
            rewrite sum_n_m_const_zero.
            rewrite Rmult_0_l. apply zero_is_0.
        - destruct n2.
          * rewrite sum_n_m_zero; try lia.
            rewrite sum_n_n.
            rewrite (coeff_mat_default _ _ _ _ v2); try lia.
            rewrite Rmult_0_r. apply zero_is_0.
          * rewrite (sum_n_m_shift _ 0 _ (S (pred (S n1)))). simpl.
            rewrite <- Nat.add_succ_comm.
            rewrite (Nat.add_comm n2 _).
            apply sum_n_m_ext_loc.
            intros k Hk.
            repeat (rewrite coeff_mat_bij; try lia).
            rewrite Hib.
            remember (k <? S n1) as r.
            induction r.
            * symmetry in Heqr. rewrite Nat.ltb_lt in Heqr. lia.
            * rewrite <- zero_is_0. reflexivity.  
Qed.

Lemma dot_concat:
    forall d1 d2 (v1: colvec d1) (v2:colvec d2) v3 v4,
      dot (colvec_concat v1 v2) (colvec_concat v3 v4) =
      dot v1 v3 + dot v2 v4.
Proof.
    intros d1 d2 v1 v2 v3 v4.
    unfold dot.
    unfold Mmult.
    repeat (rewrite coeff_mat_bij; try lia).
    unfold sum_n.
    destruct d1.
    * destruct d2.
      - simpl. repeat rewrite sum_n_n.
        repeat rewrite coeff_mat_default; try lia.
        rewrite Rmult_0_l. rewrite Rplus_0_l. reflexivity.
      - simpl.
        rewrite sum_n_n.
        rewrite coeff_mat_default; try lia.
        rewrite Rmult_0_l. rewrite Rplus_0_l.
        apply sum_n_ext_loc.
        intros n Hn.
        unfold transpose.
        unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        repeat rewrite extend_colvec_on_top_same_dim.
        simpl. repeat rewrite Rplus_0_l.
        reflexivity.
    * destruct d2.
      - simpl.
        rewrite Nat.add_0_r at 1.
        rewrite sum_n_n.
        rewrite coeff_mat_default; try lia.
        rewrite Rmult_0_l. rewrite Rplus_0_r.
        apply sum_n_m_ext_loc.
        intros k Hk. 
        unfold transpose.
        unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_on_top.
        unfold extend_colvec_at_bottom.
        unfold mk_colvec.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        destruct Hk as [Hk1 Hk2].
        apply le_lt_n_Sm in Hk2.
        rewrite <- Nat.ltb_lt in Hk2.
        rewrite Hk2. repeat rewrite Rplus_0_r.
        reflexivity.
      - rewrite (sum_n_m_Chasles _ _ (d1) (pred (S d1 + S d2))); try lia.
        apply f_equal2_plus_R.
        * simpl.
          apply sum_n_ext_loc.
          intros n Hn.
          unfold transpose.
          unfold colvec_concat.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          rewrite Nat.add_sub.
          apply le_lt_n_Sm in Hn.
          rewrite <- Nat.ltb_lt in Hn.
          rewrite Hn.
          repeat rewrite Rplus_0_r. 
          unfold coeff_colvec.
          reflexivity.
        * rewrite (sum_n_m_shift _ 0 (pred (S d2)) (S d1)).
          rewrite Nat.add_pred_l; try lia.
          rewrite (Nat.add_comm (S d2) (S d1)).
          rewrite Nat.add_0_l.
          apply sum_n_m_ext_loc.
          intros k Hk.
          unfold transpose.
          unfold colvec_concat.
          unfold Mplus.
          unfold extend_colvec_at_bottom.
          unfold extend_colvec_on_top.
          unfold mk_colvec.
          repeat (rewrite coeff_mat_bij; try lia).
          destruct Hk as [H1 H2].
          rewrite Nat.add_sub.
          rewrite <- Nat.ltb_ge in H1. rewrite H1.
          repeat rewrite Rplus_0_l.
          unfold coeff_colvec.
          reflexivity.
Qed.

Lemma colvec_split:
    forall dim1 dim2 v,
        exists v1 v2,
            v1 = (mk_colvec dim1 (fun i => coeff_colvec 0 v i)) /\
            v2 = (mk_colvec dim2 (fun i => coeff_colvec 0 v (i + dim1))) /\
            v = colvec_concat v1 v2.
Proof.
    intros dim1 dim2 v.
    exists (mk_colvec dim1 (fun i => coeff_colvec 0 v i)).
    exists (mk_colvec dim2 (fun i => coeff_colvec 0 v (i + dim1))).
    repeat (split; try reflexivity).
    unfold colvec_concat.
    unfold extend_colvec_at_bottom.
    unfold extend_colvec_on_top.
    unfold mk_colvec. unfold coeff_colvec.
    unfold Mplus.
    induction dim1.
    - induction dim2.
      * apply unique_colvec_0.
    all: (
        rewrite <- (mk_matrix_bij 0 v);
        apply mk_matrix_ext;
        intros i j Hi Hj
    ).
      * rewrite coeff_mat_bij; try lia.
        rewrite Rplus_0_l.
        rewrite coeff_mat_bij; try lia.
        rewrite Nat.sub_diag. 
        rewrite coeff_mat_bij; try lia.
        rewrite coeff_mat_bij; try lia.
        rewrite Nat.add_0_r. rewrite Nat.sub_0_r.
        induction j.
        * reflexivity.
        * lia.
    - induction j; try lia.
      rewrite coeff_mat_bij; try lia.
      remember (i <? S dim1) as r. 
      destruct r.
      * symmetry in Heqr. apply Nat.ltb_lt in Heqr.
        do 3 (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        apply Nat.ltb_lt in Heqr. rewrite Heqr.
        rewrite Rplus_0_r. reflexivity.
      * rewrite Rplus_0_l.
        rewrite coeff_mat_bij; try lia.
        rewrite Nat.add_sub.
        symmetry in Heqr.
        rewrite Heqr. apply Nat.ltb_ge in Heqr.
        rewrite coeff_mat_bij; try lia.
        rewrite coeff_mat_bij; try lia.
        rewrite Nat.sub_add; try lia.
        reflexivity.
Qed.

End ReshapeOperations.

Module MatrixNotations.

Declare Scope colvec_scope.
Delimit Scope colvec_scope with v.
Bind Scope colvec_scope with colvec.

Notation "A * B" := (dot A B) : colvec_scope.

Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.

Notation "A * B" := (Mmult A B) : matrix_scope.
Notation "A + B" := (Mplus A B) : matrix_scope.

Declare Scope scalar_scope.
Delimit Scope scalar_scope with scalar.

Notation "c * M" := (scalar_mult c M) : scalar_scope.

End MatrixNotations.
