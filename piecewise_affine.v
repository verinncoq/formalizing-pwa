From Coq Require Import Reals List Arith Lia Lra.
From Coquelicot Require Import Coquelicot.
From CoqE2EAI Require Import matrix_extensions.
Import ListNotations.
Import MatrixNotations.

Open Scope colvec_scope.
Open Scope matrix_scope.
Open Scope R_scope.
Open Scope list_scope.

Section Polehydra.

(** * Basic convex polyhedra theory

Convex polyhedron is a set that arises from a series of
linear constraints and describes set of solutions to
a linear inequalities system. We allow only non-strict
inequalities
*)

(** A linear constraint c * _ <= b *)
Inductive LinearConstraint (dim: nat) : Type :=
| Constraint (c: colvec dim) (b:R).

(** 
A predicate that a certain point x satisfies a
linear constraint, meaning c*x <= b, where c and b
are from the definition of linear constraint
*)
Definition satisfies_lc {dim: nat} (x: colvec dim) (l: LinearConstraint dim): Prop :=
match l with
| Constraint c b => (c * x)%v <= b
end.    

(* Direct evaluation of linear constraint as a function *)
Definition lc_eval {dim: nat} (x: colvec dim) (l: LinearConstraint dim): bool :=
match l with
| Constraint c b => if Rle_dec (dot c x) b then true else false
end.    

Theorem lc_eval_correct:
    forall dim (x: colvec dim) l,
        (lc_eval x l = true <-> satisfies_lc x l).
Proof.
    intros dim x l.
    induction l.
    unfold lc_eval.
    unfold satisfies_lc.
    destruct Rle_dec.
    split.
    - intros Htaut. apply r.
    - intros Hdot. reflexivity.
    split.
    - discriminate.
    - intros Hwrong. contradiction.
Qed.  

(** A convex polyhedron is described by a set of linear constraints *)
Inductive ConvexPolyhedron (dim: nat) : Type :=
| Polyhedron (constraints: list (LinearConstraint dim)).

(**
A predicate for membership inside of convex polyhedra
x is in the polyhedron <=> x satisfies all linear constraints of the polyherdron
*)
Definition in_convex_polyhedron {dim: nat} (x: colvec dim) (p: ConvexPolyhedron dim) :=
match p with
| Polyhedron lcs =>
    forall constraint, In constraint lcs ->
    satisfies_lc x constraint
end.

Fixpoint polyhedron_eval_helper {dim: nat} (l: list (LinearConstraint dim)) (x: colvec dim): bool :=
match l with
| nil => true
| lc :: next => andb (lc_eval x lc) (polyhedron_eval_helper next x)
end.

(**
Direct evaluation of polyhedron membership as a function into bool
*)
Definition polyhedron_eval {dim: nat} (x: colvec dim) (p: ConvexPolyhedron dim): bool :=
match p with
| Polyhedron constraints => polyhedron_eval_helper constraints x
end.

Theorem polyhedron_eval_correct:
    forall dim (x: colvec dim) p,
        polyhedron_eval x p = true <-> in_convex_polyhedron x p.
Proof.
    intros dim x p.
    induction p.
    unfold polyhedron_eval.
    induction constraints.
    * simpl. split. contradiction. reflexivity.
    split. unfold polyhedron_eval_helper. unfold in_convex_polyhedron.
    {
        intros H constraint HIn.
        unfold In in HIn.
        apply andb_prop in H. destruct H.
        destruct HIn.
        * rewrite <- H1. 
          apply lc_eval_correct in H.
          apply H.
        * unfold in_convex_polyhedron in IHconstraints.
          apply IHconstraints.
          apply H0. apply H1.   
    }
    {
        intros H.
        unfold polyhedron_eval_helper.
        apply andb_true_intro.
        split.
        * apply lc_eval_correct.
          unfold in_convex_polyhedron in H.
          apply H. compute. left. reflexivity.
        * apply IHconstraints.
          unfold in_convex_polyhedron.
          intros constraint HIn.
          unfold in_convex_polyhedron in H.
          apply H. unfold In. right. apply HIn.
    }
Qed.

(**
Construction of intersection of two polyhedra
*)
Definition polyhedra_intersect {dim: nat} (p1 p2: ConvexPolyhedron dim) :=
    match p1 with
    | Polyhedron l1 =>
        match p2 with 
        | Polyhedron l2 => 
            Polyhedron dim (l1 ++ l2)
        end
    end.

Theorem polyhedra_intersect_correct:
    forall dim (x: colvec dim) p1 p2,
        in_convex_polyhedron x p1 /\ in_convex_polyhedron x p2 ->
        in_convex_polyhedron x (polyhedra_intersect p1 p2).
Proof.
    intros dim x p1 p2 Hinboth.
    induction p1. induction p2.
    unfold in_convex_polyhedron.
    unfold polyhedra_intersect.
    intros constraint Hin.
    unfold in_convex_polyhedron in Hinboth.
    destruct Hinboth.
    specialize (H constraint).
    specialize (H0 constraint).
    apply in_app_or in Hin.
    destruct Hin.
    - apply (H H1).
    - apply (H0 H1).
Qed. 

End Polehydra.

(** * Constructive piecewise affine functions *)
Section PiecewiseLinear.

(**
PWAF Axiom

For all polehydra pairs (p1 p2) \in body of PWAF f
holds that if p1 and p2 intersect, the corresponding
affine functions are the same, formally: for all
x, such that x \in p1 and x\in p2 holds that

A_1 * x + b_1 = A_2 * x + b_2

where A_i, b_i are affine function parameters
associated with p_i

This guarantees that the output of PWAF is unique
*)
Definition pwaf_univalence 
    {in_dim out_dim: nat}
    (l: list (ConvexPolyhedron in_dim * ((matrix out_dim in_dim) * colvec out_dim)))
    :=
    ForallPairs (
        fun e1 e2 =>
            let p1 := fst e1 in
            let p2 := fst e2 in
                forall x,
                    in_convex_polyhedron x p1 /\ in_convex_polyhedron x p2 ->
                    let M1 := fst (snd e1) in
                    let b1 := snd (snd e1) in
                    let M2 := fst (snd e2) in
                    let b2 := snd (snd e2) in
                    ((M1 * x) + b1 = (M2 * x) + b2)%M
    ) l. 

(**
Piecewise affine function (PWAF)

A function is affine if it can be expressed as
f(x) = A*x + b 
where A is a matrix and b is a vector.

PWAF is defined by multiple polyhedra with an affine
function attached to them. To compute f(x), the value of
PWAF f on input x, one needs to find
a polyhedron to which x belongs and compute f(x)
using affine function.

Members:
- body: list of polyhedra with an associated linear function
- prop: PWAF univalence property

Hypothesis: this is a class of functions that can be
defined using a SMT solver.
*)
Record PWAF (in_dim out_dim: nat): Type := mkPLF {
    body: list (ConvexPolyhedron in_dim * ((matrix out_dim in_dim) * colvec out_dim));
    prop: pwaf_univalence body;
}.

(**
Useful invariant of pwaf_univalence: 
if pwaf_univalence holds for a list, it holds for tail of that list as well
*)
Lemma pwaf_univalence_inv:
    forall in_dim out_dim h t,
    pwaf_univalence (in_dim:=in_dim) (out_dim:=out_dim) (h :: t) -> pwaf_univalence t.
Proof.
    intros in_dim out_dim h t Hax.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b HaIn HbIn x Hinpolyh.
    unfold pwaf_univalence in Hax.
    assert (ax1 := Hax).
    unfold ForallPairs in ax1.
    specialize (ax1 a b).
    specialize (ax1 (in_cons h a t HaIn)).
    specialize (ax1 (in_cons h b t HbIn)).
    specialize (ax1 x Hinpolyh).
    apply ax1.
Qed.

(**
A point x is in domain of PWAF f, if it has 
a polehydron in body of f

Note that PWAF is not total, it is not required
for polyhedra to cover entire R^n
*)
Definition in_pwaf_domain {in_dim out_dim: nat}
    (f: PWAF in_dim out_dim)
    (x: colvec in_dim) :=  
        exists body_el, 
            (In body_el (body in_dim out_dim f)) 
                /\ in_convex_polyhedron x (fst body_el).

(** 
A predicate that describes the value of TCPLF-SO f
f(x) = f_x for a TCPLF-SO f
*)
Definition is_pwaf_value {in_dim out_dim: nat} 
    (f: PWAF in_dim out_dim) 
    (x: colvec in_dim) 
    (f_x: colvec out_dim) :=
    in_pwaf_domain f x ->
    exists body_el,
        In body_el (body in_dim out_dim f) /\
            let p := fst body_el in
            let c := fst (snd body_el) in
            let b := snd (snd body_el) in
            in_convex_polyhedron x p /\ Mplus (Mmult c x) b = f_x.

Fixpoint pwaf_eval_helper 
    {in_dim out_dim: nat}
    (body: list (ConvexPolyhedron in_dim * ((matrix (T:=R) out_dim in_dim) * colvec out_dim)))
    (x: colvec in_dim) 
    :=
    match body with
    | nil => None
    | body_el :: next => 
        match body_el with
        | (polyh, affine_f) =>
            match polyhedron_eval x polyh with
            | true => Some affine_f
            | false => pwaf_eval_helper next x
            end
        end
    end.

Lemma pwaf_eval_helper_some_in_domain:
    forall in_dim out_dim (f: PWAF in_dim out_dim) x,
        in_pwaf_domain f x ->
        exists (body_el: (ConvexPolyhedron in_dim * _)),
            pwaf_eval_helper (body in_dim out_dim f) x = Some (snd body_el).
Proof.
    intros in_dim out_dim f x Hdomain.
    induction f.
    induction body0.
    * destruct Hdomain.
      simpl in H. destruct H. contradiction.
    * simpl. induction a. induction b.
      remember (polyhedron_eval x a) as polyh_eval.
      induction polyh_eval.
      - exists ((a, (a0, b))). reflexivity.
      - specialize (IHbody0 (pwaf_univalence_inv in_dim out_dim (a,(a0,b)) body0 prop0)).
        apply IHbody0.
        unfold in_pwaf_domain.
        destruct Hdomain.
        exists (x0).
        destruct H.
        pose proof (in_inv H) as Hinv.
        destruct Hinv.
        - induction x0. induction b0.
          simpl in H0.
          apply polyhedron_eval_correct in H0.
          apply pair_equal_spec in H1.
          destruct H1.
          apply pair_equal_spec in H2.
          destruct H2.
          rewrite H1 in Heqpolyh_eval.
          rewrite H0 in Heqpolyh_eval.
          discriminate.
        - split.
          * apply H1.
          * apply H0.
Qed.

(**
Function that directly computes the value of
PWAF or outputs None if x is not in the domain
*)
Definition pwaf_eval {in_dim out_dim: nat}
    (f: PWAF in_dim out_dim)
    (x: colvec in_dim) : option (colvec out_dim)
    :=
    match pwaf_eval_helper (body in_dim out_dim f) x with
    | None => None
    | Some (M,b) => Some (Mplus (Mmult M x) b)
    end.

Theorem pwaf_eval_correct :
    forall in_dim out_dim (f: PWAF in_dim out_dim) x f_x,
        pwaf_eval f x = Some f_x <-> 
        (in_pwaf_domain f x /\ is_pwaf_value f x f_x).
Proof.
    intros in_dim out_dim f x f_x.
    unfold pwaf_eval.
    unfold is_pwaf_value.
    induction f.
    induction body0.
    * split.
      - intros Hhelper.
        unfold pwaf_eval_helper in Hhelper.
        simpl in Hhelper. discriminate.
      - intros Hvalue.
        destruct Hvalue as [Hdomain Hvalue].
        unfold in_pwaf_domain in Hdomain.
        destruct Hdomain.
        unfold In in H. simpl in H. destruct H. contradiction H.
    * induction a. induction b.
      remember (polyhedron_eval x a) as p_eval.
      induction p_eval.
      {
        split.
        - intros Hhelper.
          split.
          - unfold in_pwaf_domain.
            exists (a, (a0, b)).
            split.
            * apply in_eq.
            * symmetry in Heqp_eval.
              rewrite polyhedron_eval_correct in Heqp_eval. 
              simpl. apply Heqp_eval.
          - exists (a, (a0, b)).
            split.
            * simpl. left. reflexivity.
            split.
            * symmetry in Heqp_eval.
                rewrite polyhedron_eval_correct in Heqp_eval. 
                simpl. apply Heqp_eval.
            * simpl. unfold pwaf_eval_helper in Hhelper.
                simpl in Hhelper.
                rewrite <- Heqp_eval in Hhelper.
                inversion Hhelper. reflexivity.
        - intros Hinpwafdom.
          destruct Hinpwafdom as [Hdomain Hinpwafdom].
          specialize (Hinpwafdom Hdomain).
          unfold pwaf_eval_helper. simpl.
          rewrite <- Heqp_eval.
          destruct Hinpwafdom.
          destruct H. destruct H0.
          rewrite <- H1. simpl.
          unfold pwaf_univalence in prop0.
          unfold ForallPairs in prop0.
          assert (ax0_1 := prop0).
          specialize (ax0_1 (a, (a0, b)) x0 (in_eq _ _) H x).
          simpl in ax0_1. f_equal.
          apply ax0_1.
          split.
          * symmetry in Heqp_eval.
            apply polyhedron_eval_correct in Heqp_eval.
            apply Heqp_eval.
          * apply H0.               
      }
      {
        assert (ax0_1:=prop0).
        apply pwaf_univalence_inv in ax0_1.
        specialize (IHbody0 ax0_1).
        unfold pwaf_eval_helper. simpl.
        rewrite <- Heqp_eval.
        fold (pwaf_eval_helper body0 x).
        destruct IHbody0. 
        split.
        - intros Heval.
          specialize (H Heval).
          destruct H.
          specialize (H1 H).
          destruct H1.
          split.
          * exists x0. 
            split. 
            right. apply H1. apply H1.
          * exists x0.
            split. 
            right. apply H1. apply H1.
        - intros Hexists.
          destruct Hexists as [Hdomain Hexists].
          specialize (Hexists Hdomain).
          destruct Hexists.
          destruct H1. destruct H2.
          destruct H1.
          * rewrite <- H1 in H2.
            apply polyhedron_eval_correct in H2.
            simpl in H2.
            rewrite H2 in Heqp_eval. discriminate.
          * apply H0.
            split.
            * unfold in_pwaf_domain.
              exists x0. split.
              - apply H1.
              - apply H2. 
            * intros Hdomain2.
              unfold in_pwaf_domain in Hdomain2.
              destruct Hdomain2.
              exists x1.
              split. apply H4.
              split. apply H4.
              rewrite <- H3.
              unfold pwaf_univalence in ax0_1.
              unfold ForallPairs in ax0_1.
              apply ax0_1.
              apply H4.
              apply H1.
              split.
              apply H4.
              apply H2.
      }
Qed.
        
(**
A PWAF representation g of a real function f is a PWAF
that is equal to f everywhwere: for all x f(x) = g(x)
*)
Definition pwaf_representation {in_dim out_dim: nat} 
    (f: colvec in_dim -> colvec out_dim) 
    (g: PWAF in_dim out_dim) :=
    forall x, is_pwaf_value g x (f x).
    
(**
A function is piecewise linear if there is a PWAF representations
*)
Definition is_piecewise_linear {in_dim out_dim: nat} (f: colvec in_dim -> colvec out_dim) :=
    exists pwaf,
        pwaf_representation f pwaf.

(**
PWAF is total if the function is defined on all inputs in R^n
*)
Definition is_total {in_dim out_dim: nat} (f: PWAF in_dim out_dim) :=
    forall (x: colvec in_dim), in_pwaf_domain f x.

(**
A TPWAF is a total PWAF
*)
Definition TPWAF (in_dim out_dim: nat) := 
    { f: PWAF in_dim out_dim | is_total f }.

End PiecewiseLinear.

(** * Example proof of piecewise linearity via construction

We prove that a simple ReLU function f([x1, x2]) = [ReLU(2 * x1 + x2), x2] is
piecewise linear by constructing a corresponding TCPLF-SO 
using definition from section PiecewiseLinear
*)

Section PiecewiseLinearExample.

(**
Naive/direct defintion of the example simple ReLU function

f([x1, x2]) = [ReLU(2*x1 + x2), x2]
*)
Definition simpleReLU (x: colvec 2) :=
    let c := mk_colvec 2 (
        fun i => 
            match i with
            | 0 => 2
            | 1 => 1
            | _ => 0
            end
        ) in
    let sum := dot c x in
    let relu_result := if Rle_dec sum 0 then 0 else sum in
    mk_colvec 2 (
        fun i =>
            match i with
            | 0 => relu_result
            | 1 => coeff_colvec 0 x 1
            | _ => 0
            end
    ).

(**
Construction of TCPLF for simple ReLU finction example

TCPLF consists of:
- A polyhedron for 2 * x1 + x2 <= 0
- A polyhedron for 2 * x1 + x2 >= 0
- Proofs of axioms
*)

Definition c_vector := mk_colvec 2 (
    fun i => 
        match i with
        | 0 => 2
        | 1 => 1
        | _ => 0
        end
).
Definition minus_c_vector := scalar_mult (Ropp 1) c_vector.

Definition lincon1 := Constraint 2 c_vector 0.
Definition lincon2 := Constraint 2 minus_c_vector 0.

(** Polyhedron for 2 * x1 + x2 <= 0 *)
Definition polyhedra1 := Polyhedron 2 [lincon1].

(** Polyhedron for 2 * x1 + x2 >= 0 which is equivalent to
    - 2 * x1 - x2 <= 0 *)
Definition polyhedra2 := Polyhedron 2 [lincon2].
Definition polyhedra_simpleReLU := [polyhedra1; polyhedra2].

(** 
Function body for TCPLF-SO of simple ReLU

Polyhedron 1 -> [0, x2]     
Polyhedron 2 -> [2 * x1 + x2, x2]
*)
Definition matrix1 :=
    mk_matrix 2 2 (
        fun i j =>
            match i, j with
            | 0, 0 => 0
            | 0, 1 => 0
            | 1, 0 => 0
            | 1, 1 => 1
            | _, _ => 0
            end
    ).

Definition matrix2 :=
    mk_matrix 2 2 (
        fun i j =>
            match i, j with
            | 0, 0 => 2
            | 0, 1 => 1
            | 1, 0 => 0
            | 1, 1 => 1
            | _, _ => 0
            end
    ).

Definition simpleReLU_body := [
    (polyhedra1, (matrix1, null_vector 2)); (polyhedra2, (matrix2, null_vector 2))
].

(**
Lemma: two polyhedra intersect at exactly 2*x1 + x2 = 0

Proof requires inference in hypothesis of intersection to
arrive at 2 * x1 + x2 <= 0 and 2 * x1 + x2 >= 0 which is then
proven using Rle_anitsym
*)
Lemma simpleReLU_polyhedra_intersection:
    forall x, 
        in_convex_polyhedron x polyhedra1 /\ in_convex_polyhedron x polyhedra2 ->
        dot c_vector x = 0.
Proof.
    intros x. simpl. 
    unfold satisfies_lc.
    intros H. destruct H.
    specialize (H lincon1). specialize (H0 lincon2).
    unfold lincon1 in H. unfold lincon2 in H0.
    assert (forall dim (c: LinearConstraint dim), c = c \/ False). {
        intros dim c. left. reflexivity.
    }
    specialize (H1 2%nat lincon1) as H11.
    specialize (H1 2%nat lincon2) as H12.
    apply H in H11. apply H0 in H12.
    unfold minus_c_vector in H12.
    rewrite dot_scalar_mult in H12.
    apply Ropp_le_ge_contravar in H12.
    rewrite Ropp_0 in H12.
    rewrite Ropp_mult_distr_l in H12.
    rewrite Ropp_involutive in H12.
    rewrite Rmult_1_l in H12.
    apply Rge_le in H12.
    apply (Rle_antisym _ _ H11) in H12.
    apply H12.
Qed.

(**
Theorem: univalence holds for simple ReLU. This means
that for two polyhedra of simple ReLU, the function is uniquely
defined at their intersection

Proof: we first destruct the goal sufficiently to create a proof
goal for each polyhedra pair and then show for each pair that
the function is the same using simple_ReLU_polyhedra_intersection
lemma
*)
Theorem simpleReLU_prop:
    pwaf_univalence simpleReLU_body.
Proof.
    unfold pwaf_univalence.
    unfold ForallPairs.
    intros a b.
    unfold In. simpl.
    intros Ha Hb x Hintersect.
    assert (Hmain: 
        in_convex_polyhedron x polyhedra1 /\ in_convex_polyhedron x polyhedra2 ->
            Mplus (Mmult matrix1 x) (null_vector 2) = 
            Mplus (Mmult matrix2 x) (null_vector 2)). {
        intros Hinboth.   
        repeat rewrite Mplus_null_vector.
        repeat rewrite Mmult_dot_split.
        unfold mk_colvec.
        apply mk_matrix_ext.
        intros i j Hi Hj.
        induction i.
        * assert (Hequal: mk_matrix 2 1 (fun i _ : nat => coeff_mat 0 matrix2 0 i) = c_vector). {
            unfold c_vector. unfold mk_colvec.
            unfold matrix2. reflexivity.
            }
            rewrite Hequal.
            rewrite simpleReLU_polyhedra_intersection.
            unfold dot. unfold Mmult.
            rewrite coeff_mat_bij. unfold sum_n.
            assert (Hzero: forall n m, sum_n_m (fun _ => zero) n m = 0). {
            intros n m.
            rewrite (sum_n_m_const_zero n m).
            reflexivity.
            }
            rewrite <- (Hzero 0%nat 1%nat) at 1.
            apply sum_n_m_ext_loc. 
            intros n Hn.
            unfold transpose.
            rewrite coeff_mat_bij.
            unfold coeff_colvec.
            rewrite coeff_mat_bij.
            unfold matrix1.
            rewrite coeff_mat_bij.
            induction n.
            - rewrite Rmult_0_l. reflexivity.
            - induction n. rewrite Rmult_0_l. reflexivity.
            rewrite Rmult_0_l. reflexivity. 
            lia. lia. lia. lia. lia. lia. lia. lia.
            apply Hinboth.
        * unfold matrix1. unfold matrix2. compute. reflexivity.
    } 
    destruct Ha. destruct Hb.
    * unfold Mplus. unfold mk_colvec. apply mk_matrix_ext.
      intros i j Hi Hj.
      rewrite <- H. rewrite <- H0. simpl. reflexivity.
    * destruct H0.
      - rewrite <- H. rewrite <- H0. simpl.
        apply Hmain.
        rewrite <- H in Hintersect.
        rewrite <- H0 in Hintersect.
        simpl in Hintersect.
        apply Hintersect.
      - contradiction.
    * destruct H. destruct Hb.
      { 
        rewrite <- H. rewrite <- H0. simpl.
        symmetry. apply Hmain.
        rewrite <- H in Hintersect.
        rewrite <- H0 in Hintersect.
        destruct Hintersect. split. apply H2. apply H1. 
      }
      destruct H0.
      {
        rewrite <- H. rewrite <- H0. simpl.
        reflexivity.
      }
      - contradiction.
    - contradiction.
Qed.

(**
PWAF for simple ReLU
*)
Definition simpleReLU_PWAF := mkPLF 2 2 simpleReLU_body simpleReLU_prop.

(**
Theorem: naive definition of simple ReLU example, simpleReLU, 
is represented by PWAF and hence piecewise linear

Proof: mostly utilizes Rle_dec (x <= y) \/ ~ (x <= y) to 
arrive at four cases for each possible polyhedra and if-statement result
of the naive definition where we then show either contradiction or 
equality of function values
*)
Theorem simpleReLU_piecewise_linear:
    is_piecewise_linear simpleReLU.
Proof.
    unfold is_piecewise_linear.
    exists simpleReLU_PWAF.
    unfold pwaf_representation.
    intros x.
    unfold is_pwaf_value.
    destruct (Rle_dec (dot c_vector x) 0).
    * exists (polyhedra1, (matrix1, null_vector 2)).
      split.
      * simpl. left. reflexivity.  
      * split.
        - unfold in_convex_polyhedron.
          simpl.  
          intros constraint Hconstraint.
          destruct Hconstraint.
          rewrite <- H0.
          unfold satisfies_lc. simpl.
          apply r. contradiction.
        - rewrite Mplus_null_vector. 
          rewrite Mmult_dot_split.
          unfold simpleReLU.
          fold c_vector.
          destruct (Rle_dec (dot c_vector x) 0).
          unfold mk_colvec. 
          apply mk_matrix_ext.
          intros i j Hi Hj.
          induction i.
          rewrite dot_null_vector. reflexivity.
          induction i.
          * unfold dot.
            unfold Mmult.
            rewrite coeff_mat_bij.
            unfold sum_n. unfold sum_n_m.
            unfold Iter.iter_nat. simpl.
            unfold transpose. unfold coeff_colvec.
            unfold matrix1.
            repeat rewrite coeff_mat_bij.
            rewrite Rmult_0_l. rewrite Rplus_0_l.
            rewrite Rmult_1_l. rewrite Rplus_0_r.
            unfold coeff_colvec.
            reflexivity.
            lia. lia. lia. lia. lia. lia. lia. lia.
            lia. lia. lia. lia. lia. lia. lia. contradiction. 
    * exists (polyhedra2, (matrix2, null_vector 2)).
      split.
      * simpl. right. left. reflexivity. 
      * apply Rnot_le_gt in n. 
        split.
        - unfold in_convex_polyhedron.
          intros constraint Hconstraint.
          destruct Hconstraint.
          rewrite <- H0.
          unfold satisfies_lc. unfold lincon2.
          unfold minus_c_vector.
          rewrite dot_scalar_mult.
          rewrite <- Ropp_mult_distr_l.
          rewrite Rmult_1_l.
          rewrite <- Ropp_0.
          apply Ropp_le_contravar.
          apply Rlt_le. apply n. 
          contradiction.
        - rewrite Mplus_null_vector. 
          rewrite Mmult_dot_split.
          unfold simpleReLU.
          fold c_vector.
          destruct (Rle_dec (dot c_vector x) 0).
          apply Rle_not_gt in r. contradiction.
          unfold mk_colvec. apply mk_matrix_ext.
          intros i j Hi Hj.
          induction i.
          reflexivity.
          induction i.
          * unfold dot. unfold Mmult.
          rewrite coeff_mat_bij.
          unfold sum_n. unfold sum_n_m. unfold Iter.iter_nat.
          simpl.
          unfold transpose. unfold coeff_colvec.
          unfold matrix1.
          repeat rewrite coeff_mat_bij.
          rewrite Rmult_0_l. rewrite Rplus_0_l.
          rewrite Rmult_1_l. rewrite Rplus_0_r.
          unfold coeff_colvec.
          reflexivity.
          lia. lia. lia. lia. lia. lia.
          lia. lia. lia. lia. lia.
Qed.

(**
Lemma: for all [x1, x2], 2 * x1 + x2 <= 0 or 2 * x1 + x2 >= 0

Proof: By specializing Rle_or_lt that tells that for real numbers
holds (x <= y) or (y < x), we arrive that either 2 * x1 + x2 <= 0 or
0 <= 2 * x1 + x2 that correspond to constraints of simple ReLU polyhedra
*)
Lemma simpleReLU_full_R_split:
    forall x,
        satisfies_lc x lincon1 \/ satisfies_lc x lincon2.
Proof.
    intros x.
    unfold satisfies_lc.
    simpl.
    unfold minus_c_vector.
    rewrite dot_scalar_mult.
    rewrite <- Ropp_0 at 2.
    rewrite <- Ropp_mult_distr_l.
    rewrite Rmult_1_l.
    pose proof (Rle_or_lt (dot c_vector x) 0) as H.
    destruct H.
    * left. apply H.
    * right. apply Ropp_ge_le_contravar. apply Rle_ge. apply Rlt_le. apply H.
Qed.

(**
Theorem: simple ReLU is a total function

Proof: follows mostly from the simple_ReLU_full_R_split lemma,
we just need to show what polyhedron contains constraint needed
*)
Theorem simpleReLU_total:
    is_total simpleReLU_PWAF.
Proof.
    unfold is_total.
    unfold in_pwaf_domain.
    intros x.
    pose proof (simpleReLU_full_R_split x).
    destruct H.
    - exists (polyhedra1, (matrix1, null_vector 2)). split.
      * simpl. left. reflexivity.
      * unfold in_convex_polyhedron. simpl.
        intros constraint Hconstraint.
        destruct Hconstraint.
        rewrite <- H0. apply H.
        contradiction.
    - exists (polyhedra2, (matrix2, null_vector 2)). split.
      * simpl. right. left. reflexivity.
      * unfold in_convex_polyhedron. simpl.
        intros constraint Hconstraint.
        destruct Hconstraint.
        rewrite <- H0. apply H.
        contradiction.
Qed.

Definition simpleReLU_TPWAF: TPWAF 2 2 := 
    exist _ simpleReLU_PWAF simpleReLU_total.

End PiecewiseLinearExample. 

