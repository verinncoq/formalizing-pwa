From Coq Require Import Nat List Reals Lia Lra Arith.
Import ListNotations.

From Coquelicot Require Import Coquelicot.

From CoqE2EAI Require Import matrix_extensions piecewise_affine.
Import MatrixNotations.

Open Scope list_scope.
Open Scope matrix_scope.
Open Scope colvec_scope.
Open Scope R_scope.

Section PWAFConcatenation.

Fixpoint extend_lincons_at_bottom
    {in_dim: nat} 
    (lcs: list (LinearConstraint in_dim)) 
    (new_dim: nat): list (LinearConstraint new_dim) :=
    match lcs with 
    | [] => []
    | (Constraint c b2) :: tail =>
        Constraint new_dim (extend_colvec_at_bottom c new_dim) b2 ::
            extend_lincons_at_bottom tail new_dim
    end.

Lemma extend_lincons_at_bottom_inv:
  forall d1 d2 (c1: colvec d1) b1 lc,
    In (Constraint d1 c1 b1) lc <->
      In (Constraint (d1 + d2) (extend_colvec_at_bottom c1 (d1 + d2)) b1)
        (extend_lincons_at_bottom lc (d1 + d2)).
Proof.
    intros d1 d2 c1 b1 lc.
    induction lc.
    * simpl. reflexivity.
    * split.
      {
        intros HIn.
        unfold extend_lincons_at_bottom.
        apply in_inv in HIn.
        destruct HIn.
        - rewrite H. apply in_eq. 
        - induction a as [c_a b_a]. 
          apply in_cons.
          apply IHlc.
          apply H.
      }
      {
        intros HIn.
        unfold extend_lincons_at_bottom in HIn.
        induction a as [c_a b_a].
        apply in_inv in HIn.
        destruct HIn.
        - inversion H.
          rewrite <- H2.
          apply extend_colvec_at_bottom_preserves_equality in H1.
          rewrite <- H1.
          apply in_eq.
        - apply in_cons.
          apply IHlc.
          apply H.
      }
Qed.

Fixpoint extend_lincons_on_top
    {in_dim: nat} 
    (lcs: list (LinearConstraint in_dim))
    (new_dim: nat): list (LinearConstraint new_dim) :=
    match lcs with 
    | [] => []
    | (Constraint c b2) :: tail =>
        Constraint new_dim (extend_colvec_on_top c new_dim) b2 ::
            extend_lincons_on_top tail new_dim
    end.   
    
Lemma extend_lincons_on_top_inv:
    forall d1 d2 (c2: colvec d2) b2 lc,
      In (Constraint d2 c2 b2) lc <->
        In (Constraint (d1 + d2) (extend_colvec_on_top c2 (d1 + d2)) b2)
          (extend_lincons_on_top lc (d1 + d2)).
Proof.
  intros d1 d2 c2 b2 lc.
  induction lc.
  * simpl. reflexivity.
  * split.
    {
      intros HIn.
      unfold extend_lincons_on_top.
      apply in_inv in HIn.
      destruct HIn.
      - rewrite H. apply in_eq. 
      - induction a as [c_a b_a]. 
        apply in_cons.
        apply IHlc.
        apply H.
    }
    {
      intros HIn.
      unfold extend_lincons_on_top in HIn.
      induction a as [c_a b_a].
      apply in_inv in HIn.
      destruct HIn.
      - inversion H.
        rewrite <- H2.
        apply extend_colvec_on_top_preserves_equality in H1.
        rewrite <- H1.
        apply in_eq.
      - apply in_cons.
        apply IHlc.
        apply H.
    }
Qed.

Definition concat_polyhedra
    {in_dim1 in_dim2: nat}
    (p_f: ConvexPolyhedron in_dim1) 
    (p_g: ConvexPolyhedron in_dim2): ConvexPolyhedron (in_dim1 + in_dim2) :=
    match p_f with
    | Polyhedron l1 =>
        match p_g with
        | Polyhedron l2 => 
            Polyhedron (in_dim1 + in_dim2) 
                (extend_lincons_at_bottom l1 (in_dim1 + in_dim2) ++ 
                extend_lincons_on_top l2 (in_dim1 + in_dim2))
        end
    end.

Lemma extend_lincons_at_bottom_split:
  forall d1 d2 (v1: colvec d1) (v2: colvec d2) b 
    (constraints: list (LinearConstraint d1)),
      In (Constraint (d1 + d2) (colvec_concat v1 v2) b) 
        (extend_lincons_at_bottom constraints (d1 + d2)) ->
      v2 = null_vector d2 /\ 
      colvec_concat v1 v2 = extend_colvec_at_bottom v1 (d1 + d2).
Proof.
  intros d1 d2 v1 v2 b constraints HIn.
  induction constraints.
  * simpl in HIn. contradiction.
  * unfold extend_lincons_at_bottom in HIn.
    induction a as [c_a b_a].
    apply in_inv in HIn. 
    destruct HIn.
    - injection H.
      intros Hb Hcolvec.
      assert (Hgoal1: v2 = null_vector d2).
      {
        unfold colvec_concat in Hcolvec.
        unfold Mplus in Hcolvec.
        unfold extend_colvec_at_bottom in Hcolvec at 1.
        unfold mk_colvec in Hcolvec.
        pose proof (mk_matrix_ext (T:=R)) as Hmatrix_ext.
        specialize (Hmatrix_ext (d1 + d2)%nat 1%nat).
        specialize (Hmatrix_ext (fun i _: nat => 
                                    if i <? d1 then
                                      coeff_colvec 0 c_a i
                                    else 
                                      0)).
        specialize (Hmatrix_ext (fun i j : nat =>
                                    plus
                                      (coeff_mat zero
                                        (extend_colvec_at_bottom v1 (d1 + d2)) i j)
                                      (coeff_mat zero 
                                        (extend_colvec_on_top v2 (d1 + d2)) i j))).
        destruct Hmatrix_ext as [Hext1 Hext2].
        unfold null_vector. unfold mk_colvec.
        unfold colvec in v2.
        rewrite (coeff_mat_ext_aux 0 0 v2 _).
        intros i j Hi Hj.
        specialize (Hext2 Hcolvec (i + d1)%nat j).
        assert (Hi1: (i + d1 < d1 + d2)%nat). lia.
        specialize (Hext2 Hi1 Hj).
        assert (Hi2: (d1 <= i + d1)%nat). lia.
        rewrite <- Nat.ltb_ge in Hi2.
        rewrite Hi2 in Hext2.
        unfold extend_colvec_at_bottom in Hext2.
        unfold extend_colvec_on_top in Hext2.
        unfold mk_colvec in Hext2.
        repeat (rewrite coeff_mat_bij in Hext2; try lia).
        rewrite Nat.add_sub in Hext2.
        rewrite Hi2 in Hext2.
        rewrite Rplus_0_l in Hext2.
        rewrite Nat.add_sub in Hext2.
        rewrite coeff_mat_bij; try lia.
        symmetry. induction j. apply Hext2. lia.
      }
      split.
      * apply Hgoal1.
      * unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        remember (i <? d1) as i_d1.
        destruct i_d1.
        - rewrite Rplus_0_r. reflexivity.
        - rewrite Rplus_0_l.
          rewrite Hgoal1.
          unfold null_vector.
          unfold mk_colvec. unfold coeff_colvec.
          symmetry in Heqi_d1. rewrite Nat.ltb_ge in Heqi_d1.
          rewrite coeff_mat_bij; try lia.
          reflexivity.
    - apply IHconstraints.
      apply H.
Qed.

Lemma extend_lincons_on_top_split:
  forall d1 d2 (v1: colvec d1) (v2: colvec d2) b 
    (constraints: list (LinearConstraint d2)),
      In (Constraint (d1 + d2) (colvec_concat v1 v2) b) 
        (extend_lincons_on_top constraints (d1 + d2)) ->
      v1 = null_vector d1 /\ 
      colvec_concat v1 v2 = extend_colvec_on_top v2 (d1 + d2).
Proof.
  intros d1 d2 v1 v2 b constraints HIn.
  induction constraints.
  * simpl in HIn. contradiction.
  * unfold extend_lincons_on_top in HIn.
    induction a as [c_a b_a].
    apply in_inv in HIn. 
    destruct HIn.
    - injection H.
      intros Hb Hcolvec.
      assert (Hgoal1: v1 = null_vector d1).
      {
        unfold colvec_concat in Hcolvec.
        unfold Mplus in Hcolvec.
        unfold extend_colvec_on_top in Hcolvec at 1.
        rewrite Nat.add_sub in Hcolvec.
        unfold mk_colvec in Hcolvec.
        pose proof (mk_matrix_ext (T:=R)) as Hmatrix_ext.
        specialize (Hmatrix_ext (d1 + d2)%nat 1%nat).
        specialize (Hmatrix_ext (fun i _: nat => 
                                    if i <? d1 then
                                      0
                                    else 
                                      coeff_colvec 0 c_a (i - d1))).
        specialize (Hmatrix_ext (fun i j : nat =>
                                    plus
                                      (coeff_mat zero
                                        (extend_colvec_at_bottom v1 (d1 + d2)) i j)
                                      (coeff_mat zero 
                                        (extend_colvec_on_top v2 (d1 + d2)) i j))).
        destruct Hmatrix_ext as [Hext1 Hext2].
        unfold null_vector. unfold mk_colvec.
        unfold colvec in v1.
        rewrite (coeff_mat_ext_aux 0 0 v1 _).
        intros i j Hi Hj.
        specialize (Hext2 Hcolvec i j).
        assert (Hi1: (i < d1 + d2)%nat). lia.
        specialize (Hext2 Hi1 Hj).
        pose proof Hi as Hi_cp.
        rewrite <- Nat.ltb_lt in Hi_cp.
        rewrite Hi_cp in Hext2.
        unfold extend_colvec_at_bottom in Hext2.
        unfold extend_colvec_on_top in Hext2.
        unfold mk_colvec in Hext2.
        repeat (rewrite coeff_mat_bij in Hext2; try lia).
        rewrite Nat.add_sub in Hext2.
        rewrite Hi_cp in Hext2.
        rewrite Rplus_0_r in Hext2.
        rewrite coeff_mat_bij; try lia.
        symmetry. induction j. apply Hext2. lia.
      }
      split.
      * apply Hgoal1.
      * unfold colvec_concat.
        unfold Mplus.
        unfold extend_colvec_at_bottom.
        unfold extend_colvec_on_top.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        repeat (rewrite coeff_mat_bij; try lia).
        rewrite Nat.add_sub.
        remember (i <? d1) as i_d1.
        destruct i_d1.
        - rewrite Rplus_0_r.
          rewrite Hgoal1.
          unfold null_vector.
          unfold mk_colvec. unfold coeff_colvec.
          symmetry in Heqi_d1. rewrite Nat.ltb_lt in Heqi_d1.
          rewrite coeff_mat_bij; try lia.
          reflexivity.
        - rewrite Rplus_0_l. reflexivity.
    - apply IHconstraints.
      apply H.
Qed.

Lemma in_concat_polyhedra_inv:
    forall d1 d2 (x1: colvec d1) (x2: colvec d2) p1 p2,
        in_convex_polyhedron (colvec_concat x1 x2) (concat_polyhedra p1 p2) <->
        in_convex_polyhedron x1 p1 /\ in_convex_polyhedron x2 p2.
Proof.
    intros d1 d2 x1 x2 p1 p2.
    destruct p1 as [constraints1].
    destruct p2 as [constraints2].
    split.
    {
      unfold in_convex_polyhedron. 
      intros HIn.
      unfold in_convex_polyhedron in HIn.
      unfold concat_polyhedra in HIn.
      split.
      - intros constraint1 HcIn.
        destruct constraint1 as [c1 b1].
        specialize (HIn (Constraint _ (extend_colvec_at_bottom c1 (d1 + d2)) b1)).
        unfold satisfies_lc in HIn.
        unfold satisfies_lc.
        rewrite <- (dot_extend_at_bottom d1 d2 _ x1 x2).
        apply HIn.
        apply in_or_app.
        left.
        apply extend_lincons_at_bottom_inv.
        apply HcIn.
      - intros constraint2 HcIn.
        destruct constraint2 as [c2 b2].
        specialize (HIn (Constraint _ (extend_colvec_on_top c2 (d1 + d2)) b2)).
        unfold satisfies_lc in HIn.
        unfold satisfies_lc.
        rewrite <- (dot_extend_on_top d1 d2 _ x1 x2).
        apply HIn.
        apply in_or_app.
        right.
        apply extend_lincons_on_top_inv.
        apply HcIn.
    }
    {
      unfold in_convex_polyhedron. 
      intros HIn.
      destruct HIn as[HInx1 HInx2].
      unfold in_convex_polyhedron.
      unfold concat_polyhedra.
      intros constraint HconstraintIn.
      destruct constraint as [c b].
      apply in_app_or in HconstraintIn.
      pose proof colvec_split.
      specialize (H d1 d2 c).
      destruct H as [c_top H].
      destruct H as [c_bottom H].
      destruct H as [Hctop_def H].
      destruct H as [Hcbottom_def Hc].
      rewrite Hc.
      destruct HconstraintIn. 
      * pose proof extend_lincons_at_bottom_inv as Hinv.
        specialize (Hinv d1 d2 c_top).
        unfold satisfies_lc.
        rewrite dot_concat.
        rewrite Hc in H.
        pose proof extend_lincons_at_bottom_split as H_lin_bot_split.
        specialize (H_lin_bot_split d1 d2 c_top c_bottom b).
        specialize (H_lin_bot_split constraints1 H).
        destruct H_lin_bot_split as [H_c_bottom_def Hconcat_def].
        rewrite H_c_bottom_def.
        rewrite dot_null_vector.
        rewrite Rplus_0_r.
        rewrite Hconcat_def in H.
        specialize (Hinv b constraints1).
        apply Hinv in H.
        apply HInx1 in H.
        unfold satisfies_lc in H.
        apply H.
      * pose proof extend_lincons_on_top_inv as Hinv.
        specialize (Hinv d1 d2 c_bottom).
        unfold satisfies_lc.
        rewrite dot_concat.
        rewrite Hc in H.
        pose proof extend_lincons_on_top_split as H_lin_top_split.
        specialize (H_lin_top_split d1 d2 c_top c_bottom b).
        specialize (H_lin_top_split constraints2 H).
        destruct H_lin_top_split as [H_c_top_def Hconcat_def].
        rewrite H_c_top_def.
        rewrite dot_null_vector.
        rewrite Rplus_0_l.
        rewrite Hconcat_def in H.
        specialize (Hinv b constraints2).
        apply Hinv in H.
        apply HInx2 in H.
        unfold satisfies_lc in H.
        apply H.
    }
Qed.

Definition concat_affine_functions 
    {in_dim1 in_dim2 out_dim1 out_dim2: nat}  
    (M_f: matrix (T:=R) out_dim1 in_dim1)
    (b_f: colvec out_dim1)
    (M_g: matrix (T:=R) out_dim2 in_dim2)
    (b_g: colvec out_dim2):
    (matrix (out_dim1 + out_dim2) (in_dim1 + in_dim2) * colvec (out_dim1 + out_dim2))
    := (block_diag_matrix M_f M_g, colvec_concat b_f b_g).

Definition pwaf_concat_body_helper 
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (body_f: list 
        (ConvexPolyhedron in_dim1 
        * ((matrix (T:=R) out_dim1 in_dim1) * colvec out_dim1)))
    (body_g: list 
        (ConvexPolyhedron in_dim2 
        * ((matrix (T:=R) out_dim2 in_dim2) * colvec out_dim2)))
    :=
    map (
        fun pair =>
            match pair with 
            | (body_el_f, body_el_g) => 
            match body_el_f, body_el_g with
            | (p_f, (M_f, b_f)), (p_g, (M_g, b_g))  =>
                    (concat_polyhedra p_f p_g,
                        concat_affine_functions M_f b_f M_g b_g) 
            end
        end
    ) (list_prod body_f body_g).


Definition pwaf_concat_body  
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (f: PWAF in_dim1 out_dim1)
    (g: PWAF in_dim2 out_dim2):  
    list (ConvexPolyhedron (in_dim1 + in_dim2) 
        * ((matrix (out_dim1 + out_dim2) (in_dim1 + in_dim2)) * colvec (out_dim1 + out_dim2)))
    :=
    let body_f := (body in_dim1 out_dim1 f) in
    let body_g := (body in_dim2 out_dim2 g) in
    pwaf_concat_body_helper body_f body_g.

Lemma pwaf_concat_body_inv:
    forall in_dim1 out_dim1 in_dim2 out_dim2 
        p_f M_f b_f p_g M_g b_g 
        (f: PWAF in_dim1 out_dim1) (g: PWAF in_dim2 out_dim2),
          In (p_f, (M_f, b_f)) (body _ _ f) ->
          In (p_g, (M_g, b_g)) (body _ _ g) ->
          In (concat_polyhedra p_f p_g, concat_affine_functions M_f b_f M_g b_g)
            (pwaf_concat_body f g).
Proof.
    intros in_dim1 out_dim1 in_dim2 out_dim2 p_f M_f b_f p_g M_g b_g f g.
    intros Hbody_f Hbody_g.
    unfold pwaf_concat_body.
    unfold pwaf_concat_body_helper.
    apply in_map_iff.
    exists ((p_f, (M_f, b_f)),(p_g,(M_g, b_g))).
    split. reflexivity.
    apply in_prod_iff.
    split. apply Hbody_f. apply Hbody_g.
Qed.

Lemma pwaf_concat_body_inverse:
    forall in_dim1 out_dim1 in_dim2 out_dim2 p_fg M_fg b_fg 
        (f: PWAF in_dim1 out_dim1) (g: PWAF in_dim2 out_dim2),
        In (p_fg, (M_fg, b_fg)) (pwaf_concat_body f g) ->
        exists p_f M_f b_f p_g M_g b_g,
            In (p_f, (M_f, b_f)) (body in_dim1 out_dim1 f) /\
            In (p_g, (M_g, b_g)) (body in_dim2 out_dim2 g) /\
            p_fg = concat_polyhedra p_f p_g /\
            M_fg = block_diag_matrix M_f M_g /\
            b_fg = colvec_concat b_f b_g.
Proof.
    intros in_dim1 out_dim1 in_dim2 out_dim2 p_fg M_fg b_fg f g HIn.
    unfold pwaf_concat_body in HIn.
    unfold pwaf_concat_body_helper in HIn.
    apply in_map_iff in HIn.
    destruct HIn as [x HIn].
    destruct HIn as [Hx HIn].
    induction x as [body_el_f body_el_g].
    apply in_prod_iff in HIn.
    destruct HIn as [HInf HIng].
    destruct body_el_f as [p_f pair_f].
    destruct pair_f as [M_f b_f].
    destruct body_el_g as [p_g pair_g].
    destruct pair_g as [M_g b_g].
    exists p_f. exists M_f. exists b_f.
    exists p_g. exists M_g. exists b_g.
    split. apply HInf.
    split. apply HIng.
    apply pair_equal_spec in Hx.
    destruct Hx as [Hxp Hxfunc].
    split. symmetry. apply Hxp.
    unfold concat_affine_functions in Hxfunc.
    apply pair_equal_spec in Hxfunc.
    destruct Hxfunc as [Hmatrix Hvector].
    split. symmetry. apply Hmatrix. symmetry. apply Hvector.
Qed.

Theorem pwaf_concat_univalence
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (f: PWAF in_dim1 out_dim1)
    (g: PWAF in_dim2 out_dim2):
    pwaf_univalence (pwaf_concat_body f g).
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x HxIntersect.
    induction a as [p_fg1 pair_f_g1].
    induction b as [p_fg2 pair_f_g2].
    induction pair_f_g1 as [M_fg1 b_fg1].
    induction pair_f_g2 as [M_fg2 b_fg2].
    pose proof pwaf_concat_body_inverse as H1.
    pose proof pwaf_concat_body_inverse as H2.
    specialize (H1 in_dim1 out_dim1 in_dim2 out_dim2).
    specialize (H2 in_dim1 out_dim1 in_dim2 out_dim2).
    specialize (H1 p_fg1 M_fg1 b_fg1 f g HaIn).
    specialize (H2 p_fg2 M_fg2 b_fg2 f g HbIn).
    destruct H1 as [p_f_1 H1].
    destruct H1 as [M_f_1 H1].
    destruct H1 as [b_f_1 H1].
    destruct H1 as [p_g_1 H1].
    destruct H1 as [M_g_1 H1].
    destruct H1 as [b_g_1 H1].
    destruct H1 as [HIn_body_el_f_1 H1].
    destruct H1 as [HIn_body_el_g_1 H1].
    destruct H1 as [Hp_fg1 H1].
    destruct H1 as [HM_fg1 Hb_fg1].
    destruct H2 as [p_f_2 H2].
    destruct H2 as [M_f_2 H2].
    destruct H2 as [b_f_2 H2].
    destruct H2 as [p_g_2 H2].
    destruct H2 as [M_g_2 H2].
    destruct H2 as [b_g_2 H2].
    destruct H2 as [HIn_body_el_f_2 H2].
    destruct H2 as [HIn_body_el_g_2 H2].
    destruct H2 as [Hp_fg2 H2].
    destruct H2 as [HM_fg2 Hb_fg2].
    simpl.
    rewrite HM_fg1. rewrite Hb_fg1.
    rewrite HM_fg2. rewrite Hb_fg2.
    pose proof colvec_split as Hx.
    specialize (Hx _ _ x).
    destruct Hx as [x1 Hx].
    destruct Hx as [x2 Hx].
    destruct Hx as [Hx1def Hx].
    destruct Hx as [Hx2def Hx].
    rewrite Hx.
    repeat rewrite MMmult_block_diag_matrix. 
    repeat rewrite Mplus_colvec_concat.
    rewrite Hp_fg1 in HxIntersect.
    rewrite Hp_fg2 in HxIntersect.
    simpl in HxIntersect.
    destruct HxIntersect as [HxIn1 HxIn2].
    rewrite Hx in HxIn1.
    rewrite Hx in HxIn2.
    apply in_concat_polyhedra_inv in HxIn1.
    apply in_concat_polyhedra_inv in HxIn2.
    destruct HxIn1 as [Hx1_p_f_1 Hx2_p_g_1].
    destruct HxIn2 as [Hx1_p_f_2 Hx2_p_g_2].
    apply colvec_concat_eq.
    * induction f as [body_f Hpwaf_f].
      pose proof Hpwaf_f as Hpwaf_f_cp.
      unfold pwaf_univalence in Hpwaf_f_cp.
      unfold ForallPairs in Hpwaf_f_cp.
      specialize (Hpwaf_f_cp (p_f_1, (M_f_1, b_f_1)) (p_f_2,(M_f_2, b_f_2))).
      specialize (Hpwaf_f_cp HIn_body_el_f_1 HIn_body_el_f_2).
      specialize (Hpwaf_f_cp x1).
      simpl in Hpwaf_f_cp.
      apply Hpwaf_f_cp.
      split. apply Hx1_p_f_1. apply Hx1_p_f_2.
    * induction g as [body_g Hpwaf_g].
      pose proof Hpwaf_g as Hpwaf_g_cp.
      unfold pwaf_univalence in Hpwaf_g_cp.
      unfold ForallPairs in Hpwaf_g_cp.
      specialize (Hpwaf_g_cp (p_g_1, (M_g_1, b_g_1)) (p_g_2,(M_g_2, b_g_2))).
      specialize (Hpwaf_g_cp HIn_body_el_g_1 HIn_body_el_g_2).
      specialize (Hpwaf_g_cp x2).
      simpl in Hpwaf_g_cp.
      apply Hpwaf_g_cp.
      split. apply Hx2_p_g_1. apply Hx2_p_g_2.
Qed.

Definition pwaf_concat
    {in_dim1 in_dim2 out_dim1 out_dim2: nat} 
    (f: PWAF in_dim1 out_dim1)
    (g: PWAF in_dim2 out_dim2):
    PWAF (in_dim1 + in_dim2) (out_dim1 + out_dim2)
    :=
    mkPLF (in_dim1 + in_dim2) (out_dim1 + out_dim2) (pwaf_concat_body f g) 
        (pwaf_concat_univalence f g).

Theorem pwaf_concat_correct:
    forall in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 
      (f: PWAF in_dim1 out_dim1) (g: PWAF in_dim2 out_dim2),
      in_pwaf_domain f x1 -> is_pwaf_value f x1 f_x1 ->
      in_pwaf_domain g x2 -> is_pwaf_value g x2 g_x2 ->
      let fg   := pwaf_concat f g in
      let x    := colvec_concat x1 x2 in
      let fg_x := colvec_concat f_x1 g_x2 in
      in_pwaf_domain fg x /\ is_pwaf_value fg x fg_x.
Proof.
    intros in_dim1 in_dim2 out_dim1 out_dim2 x1 x2 f_x1 g_x2 f g.
    intros Hdomain_f Hvalue_f Hdomain_g Hvalue_g fg x fg_x.
    split.
    {
      unfold in_pwaf_domain.
      unfold in_pwaf_domain in Hdomain_f.
      unfold in_pwaf_domain in Hdomain_g.
      destruct Hdomain_f as [body_el_f Hbody_el_f].
      destruct Hdomain_g as [body_el_g Hbody_el_g].
      induction body_el_f as [p_f pair_f].
      induction pair_f as [M_f b_f].
      induction body_el_g as [p_g pair_g].
      induction pair_g as [M_g b_g].
      exists (concat_polyhedra p_f p_g,
      concat_affine_functions M_f b_f M_g b_g).
      split.
      - unfold fg.
        unfold pwaf_concat. simpl.
        unfold pwaf_concat_body.
        apply pwaf_concat_body_inv.
        - apply Hbody_el_f.
        - apply Hbody_el_g.
      - simpl.
        unfold x.
        apply in_concat_polyhedra_inv.
        split. apply Hbody_el_f. apply Hbody_el_g.
    }
    {
      unfold is_pwaf_value.
      intros Hdomain.
      pose proof Hdomain_f as Hdomain_f_cp.
      pose proof Hdomain_g as Hdomain_g_cp.
      unfold in_pwaf_domain in Hdomain.
      unfold in_pwaf_domain in Hdomain_f_cp.
      unfold in_pwaf_domain in Hdomain_g_cp.
      destruct Hdomain_f_cp as [body_el_f Hbody_el_f].
      destruct Hdomain_g_cp as [body_el_g Hbody_el_g].
      destruct body_el_f as [p_f affine_f].
      destruct body_el_g as [p_g affine_g].
      destruct affine_f as [M_f b_f].
      destruct affine_g as [M_g b_g].
      exists (concat_polyhedra p_f p_g,
        concat_affine_functions M_f b_f M_g b_g).
      split.
      - unfold fg.
        unfold body.
        unfold pwaf_concat.
        apply pwaf_concat_body_inv.
        * apply Hbody_el_f.
        * apply Hbody_el_g.
      split.
      - simpl.
        unfold x.
        apply in_concat_polyhedra_inv.
        split. 
        * apply Hbody_el_f. 
        * apply Hbody_el_g.
      - simpl.
        unfold fg_x.
        unfold x.
        rewrite MMmult_block_diag_matrix.
        rewrite Mplus_colvec_concat.
        apply colvec_concat_eq.
        * unfold is_pwaf_value in Hvalue_f.
          specialize (Hvalue_f Hdomain_f).
          destruct Hvalue_f as [body_el_val_f Hbody_el_val_f].
          destruct Hbody_el_val_f as [Hval_f_in Hbody_el_val_f].
          destruct Hbody_el_val_f as [Hval_f_x1 Hf_x1_def].
          induction f as [body_f ax_f].
          unfold pwaf_univalence in ax_f.
          unfold ForallPairs in ax_f.
          pose proof ax_f as Hax_f.
          specialize (Hax_f body_el_val_f (p_f, (M_f, b_f))).
          destruct Hbody_el_f as [Hp_f_in H_x1_p_f].
          specialize (Hax_f Hval_f_in Hp_f_in x1).
          simpl in Hax_f.
          rewrite <- Hf_x1_def.
          symmetry.
          apply Hax_f.
          split. apply Hval_f_x1. apply H_x1_p_f.
        * unfold is_pwaf_value in Hvalue_g.
          specialize (Hvalue_g Hdomain_g).
          destruct Hvalue_g as [body_el_val_g Hbody_el_val_g].
          destruct Hbody_el_val_g as [Hval_g_in Hbody_el_val_g].
          destruct Hbody_el_val_g as [Hval_g_x2 Hg_x2_def].
          induction g as [body_g ax_g].
          unfold pwaf_univalence in ax_g.
          unfold ForallPairs in ax_g.
          pose proof ax_g as Hax_g.
          specialize (Hax_g body_el_val_g (p_g, (M_g, b_g))).
          destruct Hbody_el_g as [Hp_g_in H_x2_p_g].
          specialize (Hax_g Hval_g_in Hp_g_in x2).
          simpl in Hax_g.
          rewrite <- Hg_x2_def.
          symmetry.
          apply Hax_g.
          split. apply Hval_g_x2. apply H_x2_p_g.        
    }
Qed.

End PWAFConcatenation.

(*-----------------------------------------------------------------------------------------*)

Section PWAFComposition.

Definition compose_polyhedra_helper
    {in_dim hidden_dim: nat} 
    (M: matrix hidden_dim in_dim)
    (b1: colvec hidden_dim)
    (l_f: list (LinearConstraint hidden_dim)) :=
    map (fun c => match c with
      Constraint c b2 => Constraint in_dim 
        (transpose ((transpose c) * M)%M) (b2 - (c * b1)%v)
    end) l_f. 

Definition compose_polyhedra
    {in_dim hidden_dim: nat} 
    (p_g: ConvexPolyhedron in_dim) 
    (M: matrix hidden_dim in_dim)
    (b: colvec hidden_dim)
    (p_f: ConvexPolyhedron hidden_dim) :=
    match p_g with
    | Polyhedron l1 =>
        match p_f with
        | Polyhedron l2 => 
            Polyhedron in_dim (l1 ++ compose_polyhedra_helper M b l2)
        end
    end.

Lemma in_compose_polyhedra_spec:
    forall in_dim hid_dim p_g (M: matrix hid_dim in_dim) b p_f x,
        in_convex_polyhedron x p_g ->
        in_convex_polyhedron (Mplus (Mmult M x) b) p_f ->
        in_convex_polyhedron x (compose_polyhedra p_g M b p_f).
Proof.
    intros in_dim hid_dim p_g M b p_f x HxIn HMxbIn.
    unfold in_convex_polyhedron.
    unfold compose_polyhedra.
    induction p_g as [lc_p_g].
    induction p_f as [lc_p_f].
    intros constraint Hconstraint.
    apply in_app_or in Hconstraint.
    destruct Hconstraint.
    - unfold in_convex_polyhedron in HxIn. 
      specialize (HxIn constraint H).
      apply HxIn.
    - induction lc_p_f. 
      * simpl in H. contradiction.
      * unfold compose_polyhedra_helper in H.
        induction a as [c b1].
        simpl in H.
        destruct H.
        - unfold in_convex_polyhedron in HMxbIn.
          specialize (HMxbIn (Constraint _ c b1)).
          pose proof in_eq as in_eq_cp.
          specialize (in_eq_cp _ (Constraint _ c b1) lc_p_f).
          specialize (HMxbIn in_eq_cp).
          rewrite <- H.
          unfold satisfies_lc.
          unfold satisfies_lc in HMxbIn.
          rewrite Rle_minus_r.
          unfold dot in HMxbIn.
          rewrite Mmult_distr_l in HMxbIn.
          unfold dot. rewrite transpose_transpose.
          rewrite Mmult_assoc in HMxbIn.
          assert (Htemp: forall m n (X: matrix (T:=R) m n) Y,
            coeff_mat 0 X 0 0 + coeff_mat 0 Y 0 0 = coeff_mat 0 (Mplus X Y) 0 0). {
            intros m n X Y.
            induction m.
            induction n.
            * compute. rewrite Rplus_0_l. reflexivity.
            * compute. rewrite Rplus_0_l. reflexivity.
            induction n.
            * compute. rewrite Rplus_0_l. reflexivity.
            * unfold Mplus.
              rewrite coeff_mat_bij.
              reflexivity. 
              all: lia.
          }
          rewrite Htemp.
          apply HMxbIn.
        - apply IHlc_p_f.
          * unfold in_convex_polyhedron in HMxbIn.
            unfold in_convex_polyhedron.
            intros constraint0 Hconstraint0.
            specialize (HMxbIn constraint0).
            apply (in_cons (Constraint hid_dim c b1)) in Hconstraint0.
            specialize (HMxbIn Hconstraint0) .
            apply HMxbIn.
          * apply H.
Qed.

Theorem compose_polyhedra_subset_g:
    forall in_dim hid_dim (x: colvec in_dim) A v
        (p1: ConvexPolyhedron in_dim)
        (p2: ConvexPolyhedron hid_dim),
        in_convex_polyhedron x (compose_polyhedra p1 A v p2) ->
            in_convex_polyhedron x p1.
Proof.
    intros in_dim hid_dim x A v p1 p2 Hin.
    unfold in_convex_polyhedron in Hin.
    unfold compose_polyhedra in Hin.
    induction p1. induction p2.
    unfold in_convex_polyhedron.
    intros constraint Hconstraint.
    specialize (Hin constraint).
    apply Hin. apply in_or_app.
    left. apply Hconstraint.
Qed.

Theorem compose_polyhedra_subset_f:
    forall in_dim hid_dim (x: colvec in_dim) A v
        (p1: ConvexPolyhedron in_dim)
        (p2: ConvexPolyhedron hid_dim),
        in_convex_polyhedron x (compose_polyhedra p1 A v p2) ->
            in_convex_polyhedron (Mplus (Mmult A x) v) p2.
Proof.
    intros in_dim hid_dim x A v p1 p2 Hin.
    induction p1 as [constrs1]. induction p2 as [constrs2].
    unfold compose_polyhedra in Hin.
    unfold in_convex_polyhedron.
    intros constraint Hconstraint.
    induction constrs2.
    * simpl in Hconstraint. contradiction.
    * apply in_inv in Hconstraint.
      destruct Hconstraint.
      - unfold in_convex_polyhedron in Hin.
        induction a.
        remember (Constraint in_dim (transpose (Mmult (transpose c) A)) (b - (dot c v)))
            as composed_constraint.
        specialize (Hin composed_constraint).
        assert (HcomposedIn: In composed_constraint (constrs1 ++ 
            compose_polyhedra_helper A v (Constraint hid_dim c b :: constrs2))). {
            apply in_or_app.
            right.
            unfold compose_polyhedra_helper.
            rewrite Heqcomposed_constraint.
            simpl. left. reflexivity. 
        }
        specialize (Hin HcomposedIn).
        rewrite Heqcomposed_constraint in Hin.
        unfold satisfies_lc in Hin.
        rewrite <- H. 
        unfold satisfies_lc. 
        rewrite dot_Mplus_distr.
        apply Rle_minus_r.
        rewrite dot_Mmult.
        apply Hin.
      - apply IHconstrs2.
        unfold in_convex_polyhedron.
        intros contsraint0 Hconstraint0.
        unfold in_convex_polyhedron in Hin.
        specialize (Hin contsraint0).
        apply Hin.
        apply in_or_app.
        apply in_app_or in Hconstraint0.
        destruct Hconstraint0.
        * left. apply H0.
        * right.  
          unfold compose_polyhedra_helper.
          induction a.
          fold (compose_polyhedra_helper (in_dim:=in_dim) (hidden_dim:=hid_dim)).
          apply in_cons.
          apply H0.
        apply H.
Qed.

Definition compose_affine_functions 
    {in_dim hidden_dim out_dim: nat} 
    (M_f: matrix (T:=R) out_dim hidden_dim)
    (b_f: colvec out_dim)
    (M_g: matrix (T:=R) hidden_dim in_dim)
    (b_g: colvec hidden_dim)
    :=
    (M_f * M_g, (M_f * b_g) + b_f)%M.

Definition pwaf_compose_body_helper 
    {in_dim hidden_dim out_dim: nat} 
    (body_f: list 
        (ConvexPolyhedron hidden_dim * ((matrix (T:=R) out_dim hidden_dim) * colvec out_dim)))
    (body_g: list 
        (ConvexPolyhedron in_dim * ((matrix (T:=R) hidden_dim in_dim) * colvec hidden_dim)))
    :=
    map (
        fun pair =>
            match pair with 
            | (body_el_f, body_el_g) => 
            match body_el_f, body_el_g with
            | (p_f, (M_f, b_f)), (p_g, (M_g, b_g))  =>
                    (compose_polyhedra p_g M_g b_g p_f, 
                        compose_affine_functions M_f b_f M_g b_g) 
            end
        end
    ) (list_prod body_f body_g).

Definition pwaf_compose_body  
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF hidden_dim out_dim)
    (g: PWAF in_dim hidden_dim):  
    list (ConvexPolyhedron in_dim * ((matrix out_dim in_dim) * colvec out_dim))
    :=
    let body_f := (body hidden_dim out_dim f) in
    let body_g := (body in_dim hidden_dim g) in
    pwaf_compose_body_helper body_f body_g.

Theorem pwaf_compose_univalence
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF hidden_dim out_dim)
    (g: PWAF in_dim hidden_dim) :
    pwaf_univalence (pwaf_compose_body f g).
Proof.
    induction f as [body_f ax_f]. 
    induction g as [body_g ax_g].
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros body_el_c13 body_el_c24.
    induction body_el_c13 as [p_c13 pair_c13]. 
    induction pair_c13 as [A13 v13].
    induction body_el_c24 as [p_c24 pair_c24].
    induction pair_c24 as [A24 v24].
    intros Hpc13In Hpc24In x HxIncc. simpl.
    unfold pwaf_compose_body in Hpc13In.
    unfold pwaf_compose_body in Hpc24In.
    unfold pwaf_compose_body_helper in Hpc13In.
    unfold pwaf_compose_body_helper in Hpc24In.
    apply in_map_iff in Hpc13In.
    apply in_map_iff in Hpc24In.
    destruct Hpc13In as [pc13_exists_x Hpc13In].
    destruct Hpc24In as [pc24_exists_x Hpc24In].
    destruct Hpc13In as [H13_def Hpc13In].
    destruct Hpc24In as [H24_def Hpc24In].
    induction pc13_exists_x as [body_el_f_p3 body_el_g_p1].
    induction pc24_exists_x as [body_el_f_p4 body_el_g_p2].
    induction body_el_f_p3 as [p3 pair_f_3].
    induction body_el_f_p4 as [p4 pair_f_4].
    induction pair_f_3 as [A3 v3].
    induction pair_f_4 as [A4 v4].
    induction body_el_g_p1 as [p1 pair_g_1].
    induction body_el_g_p2 as [p2 pair_g_2].
    induction pair_g_1 as [A1 v1].
    induction pair_g_2 as [A2 v2].
    apply in_prod_iff in Hpc13In.
    apply in_prod_iff in Hpc24In.
    simpl in Hpc13In. simpl in Hpc24In.
    destruct Hpc13In as [Hp3In Hp1In].
    destruct Hpc24In as [Hp4In Hp2In].
    apply pair_equal_spec in H13_def.
    apply pair_equal_spec in H24_def.
    destruct H13_def as [Hpc13_def Htemp1].
    destruct H24_def as [Hpc24_def Htemp2].
    apply pair_equal_spec in Htemp1.
    apply pair_equal_spec in Htemp2.
    destruct Htemp1 as [HA13_def Hv13_def].
    destruct Htemp2 as [HA24_def Hv24_def].
    rewrite <- HA13_def.
    rewrite <- Hv13_def.
    rewrite <- HA24_def.
    rewrite <- Hv24_def.
    repeat rewrite Mplus_assoc.
    repeat rewrite <- Mmult_assoc.
    simpl in HxIncc. destruct HxIncc as [HxIn_pc13 HxIn_pc24].
    rewrite <- Hpc13_def in HxIn_pc13.
    rewrite <- Hpc24_def in HxIn_pc24.
    repeat rewrite <- Mmult_distr_l.
    assert (Hp1p2: Mplus (Mmult A1 x) v1 = Mplus (Mmult A2 x) v2). {
        pose proof ax_g as Hax_g.
        unfold pwaf_univalence in Hax_g.
        unfold ForallPairs in Hax_g.
        specialize (Hax_g (p1, (A1, v1)) (p2, (A2, v2)) Hp1In Hp2In x).
        simpl in Hax_g. apply Hax_g.
        apply compose_polyhedra_subset_g in HxIn_pc13.
        apply compose_polyhedra_subset_g in HxIn_pc24.
        split.
        - apply HxIn_pc13.
        - apply HxIn_pc24.
    }
    rewrite Hp1p2.
    pose proof ax_f as Hax_f.
    unfold pwaf_univalence in Hax_f.
    unfold ForallPairs in Hax_f.
    specialize (Hax_f (p3, (A3, v3)) (p4, (A4, v4)) Hp3In Hp4In).
    specialize (Hax_f (Mplus (Mmult A2 x) v2)).
    apply Hax_f. 
    split.
    * apply compose_polyhedra_subset_f in HxIn_pc13.
      rewrite Hp1p2 in HxIn_pc13.
      apply HxIn_pc13.
    * apply compose_polyhedra_subset_f in HxIn_pc24.
      apply HxIn_pc24.
Qed.

Definition pwaf_compose
    {in_dim hidden_dim out_dim: nat} 
    (f: PWAF hidden_dim out_dim)
    (g: PWAF in_dim hidden_dim):
    PWAF in_dim out_dim 
    :=
    mkPLF in_dim out_dim (pwaf_compose_body f g) (pwaf_compose_univalence f g).

Lemma pwaf_compose_body_inv:
    forall in_dim hid_dim out_dim pf Mf bf pg Mg bg
        (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim),
        In (pg, (Mg, bg)) (body in_dim hid_dim g) ->
        In (pf, (Mf, bf)) (body hid_dim out_dim f) ->
        let body_el_c := (
            compose_polyhedra pg Mg bg pf, 
            compose_affine_functions Mf bf Mg bg
        ) in
        In body_el_c (body _ _ (pwaf_compose f g)).
Proof.
    intros in_dim hid_dim out_dim pf Mf bf pg Mg bg f g HIng HInf body_el_c.
    unfold body_el_c.
    unfold pwaf_compose. simpl.
    unfold pwaf_compose_body.
    unfold pwaf_compose_body_helper.
    apply in_map_iff.
    exists ((pf, (Mf, bf)), (pg, (Mg, bg))).
    split. reflexivity.
    apply in_prod.
    apply HInf. apply HIng.
Qed.

Theorem pwaf_compose_correct:
    forall in_dim hid_dim out_dim x f_x g_x 
        (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim),
        in_pwaf_domain g x   -> is_pwaf_value g x g_x ->
        in_pwaf_domain f g_x -> is_pwaf_value f g_x f_x ->
        let fg := pwaf_compose f g in
        in_pwaf_domain fg x /\ is_pwaf_value fg x f_x.
Proof.
    intros in_dim hid_dim out_dim x f_x g_x f g Hdomg Hvalg Hdomf Hvalf fg.
    split.
    {
        unfold fg.
        unfold in_pwaf_domain.
        specialize (Hvalg Hdomg).
        destruct Hvalg as [body_el_g Hbody_el_g].
        induction body_el_g as [pg pair_g].
        induction pair_g as [Ag vg].
        destruct Hbody_el_g as [HpgIn Hbody_el_g].
        destruct Hbody_el_g as [HxInpg Hg_xdef].      
        unfold in_pwaf_domain in Hdomf.
        destruct Hdomf as [body_el_f Hbody_el_f].
        destruct Hbody_el_f as [HpfIn Hg_xInPf].
        induction body_el_f as [pf pair_f].
        induction pair_f as [Af vf].
        exists (compose_polyhedra pg Ag vg pf, 
            compose_affine_functions Af vf Ag vg).
        split.
        - pose proof pwaf_compose_body_inv as H.
          specialize (H in_dim hid_dim out_dim).
          specialize (H pf Af vf pg Ag vg f g).
          specialize (H HpgIn HpfIn).
          apply H.
        - simpl.
          apply in_compose_polyhedra_spec. apply HxInpg.
          rewrite <- Hg_xdef in Hg_xInPf.
          apply Hg_xInPf.
    } 
    {
        unfold is_pwaf_value.
        intros Hxfgdomain.
        unfold is_pwaf_value in Hvalf.
        specialize (Hvalf Hdomf).
        destruct Hvalf as [body_el_f Hbody_el_f].
        destruct Hbody_el_f as [Hbody_el_f_def Hbody_el_f].
        destruct Hbody_el_f as [Hg_x_in Hf_xdef].
        unfold is_pwaf_value in Hvalg.
        specialize (Hvalg Hdomg).
        destruct Hvalg as [body_el_g Hbody_el_g].
        destruct Hbody_el_g as [Hbody_el_g_def Hbody_el_g].
        destruct Hbody_el_g as [HxIn Hg_xdef].
        induction body_el_g as [pg pair_g].
        induction pair_g as [Ag vg].
        induction body_el_f as [pf pair_f].
        induction pair_f as [Af vf].
        exists (compose_polyhedra pg Ag vg pf, 
        compose_affine_functions Af vf Ag vg).
        split.
        - unfold fg.
          unfold pwaf_compose.
          unfold pwaf_compose_body. simpl.
          apply pwaf_compose_body_inv.
          apply Hbody_el_g_def. apply Hbody_el_f_def.
        split.
        - simpl.
          apply in_compose_polyhedra_spec. apply HxIn.
          simpl in Hg_xdef.
          rewrite Hg_xdef.
          apply Hg_x_in.
        - simpl. simpl in Hf_xdef.
          rewrite <- Hf_xdef.
          rewrite <- Hg_xdef. simpl.
          rewrite Mplus_assoc.
          rewrite Mmult_distr_l.
          rewrite Mmult_assoc.
          reflexivity.
    }
Qed.
    
End PWAFComposition.

(*-----------------------------------------------------------------------------------------*)

Section PWAFOperationsProperties.

Theorem pwaf_compose_reverse_domain_f:
    forall in_dim hid_dim out_dim 
    (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim) fg x g_x,
     fg = pwaf_compose f g ->
     in_pwaf_domain fg x ->
     is_pwaf_value g x g_x ->
     in_pwaf_domain f g_x.
Proof.
    intros in_dim hid_dim out_dim f g fg x g_x Hfg Hxdomfg Hvalg_x.
    unfold in_pwaf_domain in Hxdomfg.
    rewrite Hfg in Hxdomfg.
    simpl in Hxdomfg.
    destruct Hxdomfg as [p_fg Hpfg].
    destruct Hpfg as [HpfgIn Hxpfg].
    unfold pwaf_compose_body in HpfgIn.
    unfold pwaf_compose_body_helper in HpfgIn.
    apply in_map_iff in HpfgIn.
    destruct HpfgIn as [prod_el Hpfg].
    destruct Hpfg as [Hpfg_def Hpfg_In].
    destruct prod_el as [body_el_f body_el_g].
    apply in_prod_iff in Hpfg_In.
    destruct Hpfg_In as [Hbody_el_f_In Hbody_el_g_In].
    unfold in_pwaf_domain.
    exists body_el_f.
    destruct body_el_f as [p_f affine_f].
    destruct body_el_g as [p_g affine_g].
    destruct affine_g as [M_g b_g].
    destruct affine_f as [M_f b_f].
    split; try apply Hbody_el_f_In.
    rewrite <- Hpfg_def in Hxpfg.
    simpl in Hxpfg.
    unfold is_pwaf_value in Hvalg_x.
    assert (Hx_dom_g: in_pwaf_domain g x). {
      unfold in_pwaf_domain.
      exists (p_g, (M_g, b_g)).
      split; try apply Hbody_el_g_In.
      apply compose_polyhedra_subset_g in Hxpfg.
      apply Hxpfg.
    }
    pose proof Hxpfg as Hxpg.
    apply compose_polyhedra_subset_f in Hxpfg.
    apply Hvalg_x in Hx_dom_g.
    destruct Hx_dom_g as [body_el_g_2 Hbody_el_g_2].
    destruct Hbody_el_g_2 as [Hbody_el_g_2_In Hx_In_body_el_g_2].
    destruct Hx_In_body_el_g_2 as [Hx_In_body_el_g_2 Hgx_def].
    apply compose_polyhedra_subset_g in Hxpg.
    destruct g as [body_g ax_g].
    pose proof ax_g as Hax_g.
    unfold pwaf_univalence in Hax_g.
    unfold ForallPairs in Hax_g.
    specialize (Hax_g (p_g, (M_g, b_g)) body_el_g_2).
    specialize (Hax_g Hbody_el_g_In Hbody_el_g_2_In x).
    assert (H_x_in_pg_pg2: in_convex_polyhedron x p_g /\ 
                           in_convex_polyhedron x (fst body_el_g_2)). auto.
    specialize (Hax_g H_x_in_pg_pg2).
    destruct body_el_g_2 as [p_g_2 affine_g_2].
    destruct affine_g_2 as [M_g_2 b_g_2].
    rewrite <- Hgx_def.
    simpl. simpl in Hax_g.
    rewrite <- Hax_g.
    apply Hxpfg.
Qed.

Theorem pwaf_compose_reverse_value_f:
    forall in_dim hid_dim out_dim 
    (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim) fg x g_x fg_x,
     fg = pwaf_compose f g ->
     in_pwaf_domain fg x ->
     is_pwaf_value fg x fg_x ->
     is_pwaf_value g x g_x ->
     is_pwaf_value f g_x fg_x.
Proof.
    intros in_dim hid_dim out_dim f g fg x g_x fg_x.
    intros Hfg_def Hx_dom_fg Hfgx_def Hgx_def.
    unfold is_pwaf_value.
    intros Hf_dom.
    unfold in_pwaf_domain in Hf_dom.
    destruct Hf_dom as [body_el_f Hbody_el_f].
    exists body_el_f.
    repeat (split; try apply Hbody_el_f).
    destruct body_el_f as [p_f affine_f].
    destruct affine_f as [M_f b_f].
    destruct Hbody_el_f as [Hbody_el_f_In H_gx_pf].
    simpl.
    unfold is_pwaf_value in Hfgx_def.
    apply Hfgx_def in Hx_dom_fg.
    destruct Hx_dom_fg as [body_el_fg Hbody_el_fg].
    destruct Hbody_el_fg as [Hbody_el_fg_In Hx_body_el_fg].
    destruct Hx_body_el_fg as [Hx_body_el_fg Hfgx_value].
    rewrite Hfg_def in Hbody_el_fg_In.
    simpl in Hbody_el_fg_In.
    unfold pwaf_compose_body in Hbody_el_fg_In.
    unfold pwaf_compose_body_helper in Hbody_el_fg_In.
    apply in_map_iff in Hbody_el_fg_In.
    destruct Hbody_el_fg_In as [body_els_f_g Hbody_el_fg].
    destruct Hbody_el_fg as [Hbody_el_fg_def Hbody_els].
    destruct body_els_f_g as [body_el_f_2 body_el_g].
    destruct body_el_g as [p_g affine_g].
    destruct body_el_f_2 as [p_f_2 affine_f_2].
    apply in_prod_iff in Hbody_els.
    destruct Hbody_els as [Hbody_el_f_2_In Hbody_el_g_In].
    destruct affine_g as [M_g b_g].
    destruct affine_f_2 as [M_f_2 b_f_2].
    rewrite <- Hbody_el_fg_def in Hfgx_value.
    simpl in Hfgx_value.
    unfold is_pwaf_value in Hgx_def.
    assert (Hx_dom_g: in_pwaf_domain g x). {
      unfold in_pwaf_domain.
      exists (p_g, (M_g, b_g)).
      split. apply Hbody_el_g_In.
      rewrite <- Hbody_el_fg_def in Hx_body_el_fg.
      simpl in Hx_body_el_fg.
      apply compose_polyhedra_subset_g in Hx_body_el_fg.
      apply Hx_body_el_fg.
    }
    apply Hgx_def in Hx_dom_g.
    destruct Hx_dom_g as [body_el_g_2 Hbody_el_g_2].
    destruct Hbody_el_g_2 as [Hbody_el_g_2_In Hbody_el_g_2].
    destruct Hbody_el_g_2 as [Hx_body_el_g_2 Hgx_def_2].
    destruct g as [body_g pwaf_ax_g].
    pose proof pwaf_ax_g as Hpwaf_ax_g.
    unfold pwaf_univalence in Hpwaf_ax_g.
    unfold ForallPairs in Hpwaf_ax_g.
    specialize (Hpwaf_ax_g (p_g, (M_g, b_g)) body_el_g_2).
    destruct body_el_g_2 as [p_g_2 affine_g_2].
    destruct affine_g_2 as [M_g_2 b_g_2].
    specialize (Hpwaf_ax_g Hbody_el_g_In Hbody_el_g_2_In x).
    assert (H_x_intersection: in_convex_polyhedron x p_g /\ 
                              in_convex_polyhedron x p_g_2). {
        split; auto.
        rewrite <- Hbody_el_fg_def in Hx_body_el_fg.
        apply compose_polyhedra_subset_g in Hx_body_el_fg.
        apply Hx_body_el_fg.
    }
    specialize (Hpwaf_ax_g H_x_intersection).
    simpl in Hpwaf_ax_g.
    simpl in Hgx_def_2.
    rewrite <- Hpwaf_ax_g in Hgx_def_2.
    destruct f as [body_f pwaf_ax_f].
    pose proof pwaf_ax_f as Hpwaf_ax_f.
    unfold pwaf_univalence in Hpwaf_ax_f.
    unfold ForallPairs in Hpwaf_ax_f.
    specialize (Hpwaf_ax_f (p_f, (M_f, b_f)) (p_f_2, (M_f_2, b_f_2))).
    specialize (Hpwaf_ax_f Hbody_el_f_In Hbody_el_f_2_In g_x).
    assert (H_gx_intersection: in_convex_polyhedron g_x p_f /\ 
                              in_convex_polyhedron g_x p_f_2). {
        split; auto.
        rewrite <- Hbody_el_fg_def in Hx_body_el_fg.
        apply compose_polyhedra_subset_f in Hx_body_el_fg.
        rewrite Hgx_def_2 in Hx_body_el_fg.
        apply Hx_body_el_fg.
    }
    specialize (Hpwaf_ax_f H_gx_intersection).
    simpl in Hpwaf_ax_f.
    rewrite Hpwaf_ax_f.
    rewrite <- Hgx_def_2.
    rewrite <- Hfgx_value.
    rewrite Mmult_distr_l.
    rewrite Mplus_assoc.
    rewrite Mmult_assoc.
    reflexivity.
Qed.

Theorem pwaf_compose_reverse_domain_g:
    forall in_dim hid_dim out_dim 
    (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim) fg x,
    fg = pwaf_compose f g ->
    in_pwaf_domain fg x -> 
    in_pwaf_domain g x.
Proof.
    intros in_dim hid_dim out_dim f g fg x Hfg_def Hx_dom_fg.
    unfold in_pwaf_domain.
    rewrite Hfg_def in Hx_dom_fg.
    unfold in_pwaf_domain in Hx_dom_fg.
    destruct Hx_dom_fg as [body_el_fg Hbody_el_fg_In].
    destruct Hbody_el_fg_In as [Hbody_el_fg_In Hx_p_fg].
    unfold pwaf_compose in Hbody_el_fg_In.
    unfold pwaf_compose_body in Hbody_el_fg_In.
    simpl in Hbody_el_fg_In.
    unfold pwaf_compose_body_helper in Hbody_el_fg_In.
    apply in_map_iff in Hbody_el_fg_In.
    destruct Hbody_el_fg_In as [body_els Hbody_els].
    destruct body_els as [body_el_f body_el_g].
    destruct Hbody_els as [Hbody_el_fg_def Hbody_els_In].
    apply in_prod_iff in Hbody_els_In.
    destruct Hbody_els_In as [Hbody_el_f_In Hbody_el_g_In].
    exists body_el_g. split. apply Hbody_el_g_In.
    destruct body_el_f as [p_f affine_f].
    destruct affine_f as [M_f b_f].
    destruct body_el_g as [p_g affine_g].
    destruct affine_g as [M_g b_g].
    rewrite <- Hbody_el_fg_def in Hx_p_fg.
    simpl in Hx_p_fg.
    apply compose_polyhedra_subset_g in Hx_p_fg.
    apply Hx_p_fg.
Qed.

Theorem pwaf_compose_reverse_value_g:
    forall in_dim hid_dim out_dim 
    (f: PWAF hid_dim out_dim) (g: PWAF in_dim hid_dim) fg x,
    fg = pwaf_compose f g ->
    in_pwaf_domain fg x -> 
    exists g_x, 
      is_pwaf_value g x g_x.
Proof.
    intros in_dim hid_dim out_dim f g fg x Hfg_def Hx_dom_fg. 
    unfold in_pwaf_domain.
    rewrite Hfg_def in Hx_dom_fg.
    unfold in_pwaf_domain in Hx_dom_fg.
    destruct Hx_dom_fg as [body_el_fg Hbody_el_fg_In].
    destruct Hbody_el_fg_In as [Hbody_el_fg_In Hx_p_fg].
    unfold pwaf_compose in Hbody_el_fg_In.
    unfold pwaf_compose_body in Hbody_el_fg_In.
    simpl in Hbody_el_fg_In.
    unfold pwaf_compose_body_helper in Hbody_el_fg_In.
    apply in_map_iff in Hbody_el_fg_In.
    destruct Hbody_el_fg_In as [body_els Hbody_els].
    destruct body_els as [body_el_f body_el_g].
    destruct Hbody_els as [Hbody_el_fg_def Hbody_els_In].
    apply in_prod_iff in Hbody_els_In.
    destruct Hbody_els_In as [Hbody_el_f_In Hbody_el_g_In].
    destruct body_el_f as [p_f affine_f].
    destruct affine_f as [M_f b_f].
    destruct body_el_g as [p_g affine_g].
    destruct affine_g as [M_g b_g].
    exists (Mplus (Mmult M_g x) b_g).
    unfold is_pwaf_value.
    intros Hdomain_g_x.
    exists ((p_g, (M_g, b_g))).
    split. 
    * apply Hbody_el_g_In.
    split.
    * rewrite <- Hbody_el_fg_def in Hx_p_fg.
      apply compose_polyhedra_subset_g in Hx_p_fg.
      apply Hx_p_fg.
    * simpl. reflexivity. 
Qed.   

End PWAFOperationsProperties.

