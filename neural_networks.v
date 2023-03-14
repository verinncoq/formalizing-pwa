From Coq Require Import Reals Lia Lra.

From Coquelicot Require Import Coquelicot.

From CoqE2EAI Require Import matrix_extensions piecewise_affine neuron_functions pwaf_operations.

Open Scope R_scope.

Section SequentialNeuralNetworks.

Inductive NNSequential {input_dim output_dim: nat} :=
| NNOutput : NNSequential
| NNPlainLayer {hidden_dim: nat}:
    (colvec input_dim -> colvec hidden_dim)
    -> NNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)
    -> NNSequential
| NNPWALayer {hidden_dim: nat}:
    PWAF input_dim hidden_dim 
    -> NNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)
    -> NNSequential
| NNUnknownLayer {hidden_dim: nat}:
    NNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)
    -> NNSequential.


Definition NNLinear 
    {input_dim hidden_dim output_dim: nat} 
    (W: matrix hidden_dim input_dim) 
    (b: colvec hidden_dim) 
    (NNnext: NNSequential (input_dim:=hidden_dim) (output_dim:=output_dim)) :=
    NNPWALayer (LinearPWAF W b) NNnext.

Definition NNReLU
    {input_dim output_dim: nat} 
    (NNnext: NNSequential (input_dim:=input_dim) (output_dim:=output_dim)) :=
    NNPWALayer (input_dim:=input_dim) ReLU_PWAF NNnext.
    
End SequentialNeuralNetworks.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNeuralNetworkExample.

Definition example_weights: matrix 2 2 :=
    [[2.7, 0   ],
     [1,   0.01]].

Definition example_biases: colvec 2 :=
    [[1   ], 
     [0.25]].

Definition example_nn := 
    (NNLinear example_weights example_biases 
    (NNReLU
    (NNOutput (output_dim:=2)))).
    
End SequentialNeuralNetworkExample.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNeuralNetworkExample2.

Definition example_weights2 :=
    mk_matrix 2 2 (fun i j =>
        match i, j with
        | 0, 0 => 1
        | 0, 1 => 1
        | 1, 0 => 1
        | 1, 1 => 1
        | _, _ => 0
        end
    ).

Definition example_biases2 :=
    mk_colvec 2 (fun i =>
        match i with
        | 0 => 1
        | 1 => 0.25
        | _ => 0
        end
    ).

Definition example2 := 
    (NNLinear (input_dim:=2) example_weights2 example_biases2
    (NNReLU
    (NNLinear example_weights2 example_biases2 
    (NNOutput (output_dim:=2))))).
    
End SequentialNeuralNetworkExample2.

(*-----------------------------------------------------------------------------------------*)

Section SequentialNetworkEvaluation.

Definition flex_dim_copy {input_dim output_dim: nat} 
    (x: colvec input_dim): colvec output_dim 
    :=
    Mmult (mk_matrix output_dim input_dim Mone_seq) x.

Fixpoint nn_eval {in_dim out_dim: nat} 
    (nn: NNSequential (input_dim:=in_dim) (output_dim:=out_dim)) 
    (input: colvec in_dim): option (colvec out_dim)
    := 
    match nn with
        | NNOutput => Some (flex_dim_copy input)
        | NNPlainLayer _ f next_layer => 
            nn_eval next_layer (f input)
        | NNPWALayer _ pwaf next_layer => 
            match pwaf_eval pwaf input with
            | Some output => nn_eval next_layer output
            | None => None
            end  
        | NNUnknownLayer _ _ => 
            None
    end.

End SequentialNetworkEvaluation.

Section PWAF_conversion.

Fixpoint transform_nn_to_pwaf {in_dim out_dim: nat}
    (nn: NNSequential (input_dim := in_dim) (output_dim := out_dim)) 
    : option (PWAF in_dim out_dim) :=
    match nn with
        | NNOutput => Some (OutputPWAF)
        | NNPlainLayer _ _ _ => None
        | NNPWALayer _ pwaf next => 
            match transform_nn_to_pwaf next with
            | Some next_pwaf => Some (pwaf_compose next_pwaf pwaf)
            | None => None
            end
        | NNUnknownLayer _ _ => None
    end.
    
Theorem transform_nn_to_pwaf_correct:
    forall in_dim out_dim (x: colvec in_dim) (f_x: colvec out_dim) nn nn_pwaf,
        Some nn_pwaf = transform_nn_to_pwaf nn ->
        in_pwaf_domain nn_pwaf x ->
        is_pwaf_value nn_pwaf x f_x <-> nn_eval nn x = Some f_x.
Proof.
    intros in_dim out_dim x f_x nn nn_pwaf Hrepr Hdomain.
    induction nn; try (unfold transform_nn_to_pwaf in Hrepr; discriminate).
    * unfold transform_nn_to_pwaf in Hrepr.
      injection Hrepr. 
      intros Hnn_pwaf. 
      split.
      {
        intros Hvalue.
        unfold nn_eval.
        unfold is_pwaf_value in Hvalue.
        specialize (Hvalue Hdomain).
        unfold flex_dim_copy.
        f_equal.
        destruct Hvalue as [body_el Hvalue].
        destruct Hvalue as [HIn Hvalue].
        destruct Hvalue as [Hopy Hvalue].
        rewrite <- Hvalue.
        rewrite Hnn_pwaf in HIn.
        unfold body in HIn.
        unfold OutputPWAF in HIn.
        unfold LinearPWAF in HIn.
        unfold linear_body in HIn.
        unfold List.In in HIn.
        destruct HIn; try contradiction.
        rewrite <- H. simpl.
        rewrite Mplus_null_vector.
        reflexivity.
      }
      {
        intros Hnneval.
        unfold is_pwaf_value.
        intros Hdomain2.
        rewrite Hnn_pwaf.
        exists (full_R_polyhedron input_dim, 
            (mk_matrix output_dim input_dim Mone_seq, null_vector output_dim)).
        split.
        - unfold OutputPWAF. unfold LinearPWAF.
          unfold body. unfold linear_body.
          simpl. left. reflexivity.
        split.
        - rewrite Hnn_pwaf in Hdomain2.
          unfold in_pwaf_domain in Hdomain2.
          destruct Hdomain2 as [body_el_dom Hbody_el_dom].
          destruct Hbody_el_dom as [Hbody_el_dom_def H_x_in_el_dom].
          unfold OutputPWAF in Hbody_el_dom_def.
          unfold LinearPWAF in Hbody_el_dom_def.
          unfold linear_body in Hbody_el_dom_def.
          unfold List.In in Hbody_el_dom_def.
          simpl in Hbody_el_dom_def.
          destruct Hbody_el_dom_def; try contradiction.
          rewrite <- H in H_x_in_el_dom.
          apply H_x_in_el_dom.
        - simpl.
          unfold nn_eval in Hnneval.
          injection Hnneval.
          intros Hf_x.
          rewrite <- Hf_x.
          unfold flex_dim_copy.
          rewrite Mplus_null_vector.
          reflexivity.
      }
    * unfold transform_nn_to_pwaf in Hrepr.
      fold (transform_nn_to_pwaf nn) in Hrepr.
      remember (transform_nn_to_pwaf nn) as nn_pwaf_prev.
      destruct nn_pwaf_prev as [nn_pwaf_prev|]; try discriminate.
      injection Hrepr as Hnn_pwaf_def.
      split.
      {
        intros Hvalue.
        unfold nn_eval. fold (nn_eval nn).
        remember (pwaf_eval p x) as c_x. 
        destruct c_x as [c_x|].
        - specialize (IHnn c_x f_x nn_pwaf_prev eq_refl).
          symmetry in Heqc_x.
          apply pwaf_eval_correct in Heqc_x.
          destruct Heqc_x as [Hdomain_c_x Hvalue_c_x]. 
          pose proof pwaf_eval_correct as Heval_correct.
          specialize (Heval_correct input_dim output_dim nn_pwaf).
          specialize (Heval_correct x f_x).
          destruct Heval_correct as [Heval1 Heval2].
          pose proof pwaf_compose_reverse_domain_f as Hreverse_dom.
          specialize (Hreverse_dom input_dim hidden_dim output_dim).
          specialize (Hreverse_dom nn_pwaf_prev p nn_pwaf).
          specialize (Hreverse_dom x c_x).
          specialize (Hreverse_dom Hnn_pwaf_def Hdomain Hvalue_c_x).
          specialize (IHnn Hreverse_dom).
          apply IHnn. 
          pose proof pwaf_compose_reverse_value_f as Hreverse_val.
          specialize (Hreverse_val input_dim hidden_dim output_dim).
          specialize (Hreverse_val nn_pwaf_prev p nn_pwaf).
          specialize (Hreverse_val x c_x f_x).
          specialize (Hreverse_val Hnn_pwaf_def Hdomain Hvalue Hvalue_c_x).
          apply Hreverse_val.
        - exfalso.
          pose proof pwaf_compose_reverse_domain_g as Hreverse_dom.
          specialize (Hreverse_dom input_dim hidden_dim output_dim).
          specialize (Hreverse_dom nn_pwaf_prev p nn_pwaf x).
          specialize (Hreverse_dom Hnn_pwaf_def Hdomain).
          pose proof pwaf_compose_reverse_value_g as Hreverse_val.
          specialize (Hreverse_val input_dim hidden_dim output_dim).
          specialize (Hreverse_val nn_pwaf_prev p nn_pwaf x).
          specialize (Hreverse_val Hnn_pwaf_def Hdomain).
          destruct Hreverse_val as [c_x Hc_x].
          assert (Hjoin: in_pwaf_domain p x /\ is_pwaf_value p x c_x). auto.
          apply pwaf_eval_correct in Hjoin.
          rewrite Hjoin in Heqc_x.
          discriminate.
      }
      {
        intros Hvalue.
        unfold nn_eval in Hvalue.
        fold (nn_eval nn) in Hvalue.
        remember (pwaf_eval p x) as c_x. 
        destruct c_x as [c_x|].
        * specialize (IHnn c_x f_x nn_pwaf_prev eq_refl).
          symmetry in Heqc_x.
          apply pwaf_eval_correct in Heqc_x.
          destruct Heqc_x as [Hdomain_c_x Hvalue_c_x].
          pose proof pwaf_compose_reverse_domain_f as Hreverse_dom.
          specialize (Hreverse_dom input_dim hidden_dim output_dim).
          specialize (Hreverse_dom nn_pwaf_prev p nn_pwaf).
          specialize (Hreverse_dom x c_x).
          specialize (Hreverse_dom Hnn_pwaf_def Hdomain Hvalue_c_x).
          specialize (IHnn Hreverse_dom).
          apply IHnn in Hvalue.
          pose proof pwaf_compose_correct as Hcorrect.
          specialize (Hcorrect input_dim hidden_dim output_dim).
          specialize (Hcorrect x f_x c_x nn_pwaf_prev p).
          specialize (Hcorrect Hdomain_c_x Hvalue_c_x Hreverse_dom Hvalue).
          destruct Hcorrect as [Hcorrect_dom Hcorrect_val].
          rewrite <- Hnn_pwaf_def in Hcorrect_val.
          apply Hcorrect_val.
        * exfalso.
          pose proof pwaf_compose_reverse_domain_g as Hreverse_dom.
          specialize (Hreverse_dom input_dim hidden_dim output_dim).
          specialize (Hreverse_dom nn_pwaf_prev p nn_pwaf x).
          specialize (Hreverse_dom Hnn_pwaf_def Hdomain).
          pose proof pwaf_compose_reverse_value_g as Hreverse_val.
          specialize (Hreverse_val input_dim hidden_dim output_dim).
          specialize (Hreverse_val nn_pwaf_prev p nn_pwaf x).
          specialize (Hreverse_val Hnn_pwaf_def Hdomain).
          destruct Hreverse_val as [c_x Hc_x].
          assert (Hjoin: in_pwaf_domain p x /\ is_pwaf_value p x c_x). auto.
          apply pwaf_eval_correct in Hjoin.
          rewrite Hjoin in Heqc_x.
          discriminate.
      }
Qed.

End PWAF_conversion.