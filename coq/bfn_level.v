(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** This corresponds to bfnum on page 134 (section 4 and Figure 5) of Okasaki's article *)

Require Import List Arith Omega Wellfounded Extraction.
Require Import list_utils wf_utils zip bt bft_std bft_inj bft_forest bfn_trivial.

(* We need the (non-informative) existence of a BFN numbering for the proof to work ...
   It does not impact the CC of the following code *)

Set Implicit Arguments.

Section breadth_first_numbering_by_levels.

  Fixpoint forest_children {X: Type} (ll : list (bt X)) : nat * list (bt X) :=
    match ll with 
      | nil   => (0,nil)
      | t::l => let (n,ch) := forest_children l in
      match t with
        | leaf x     => (S n,ch)
        | node a x b => (S n,a::b::ch)
      end
    end.

  (** the following could have served as a less optimized definition *)
  Fact forest_children_eq X ll : @forest_children X ll = (length ll, subtrees ll).
  Proof. 
    induction ll as [ | [ x | a x b ] ll IH ]; simpl; auto; 
    destruct (forest_children ll) as (n,ch); auto;
    inversion IH; subst; auto.
  Qed.

  Fixpoint forest_rebuild {X: Type} (i: nat) (ts : list (bt X)) (cs: list (bt nat)): list (bt nat) :=
    match ts with 
      | nil => nil
      | leaf _ :: ts => leaf i :: forest_rebuild (S i) ts cs
      | node _ _ _ :: ts =>
      match cs with
        | a :: b :: cs => node a i b :: forest_rebuild (S i) ts cs
        | _ => nil
      end
    end.

  Lemma forest_rebuild_id (i: nat) (ts : list (bt nat)):
          is_seq_from i (roots ts) -> forest_rebuild i ts (subtrees ts) = ts.
  Proof.
    revert i.
    induction ts as [ | [|] ]; simpl; auto; intros ? []; subst; f_equal; auto.
  Qed.

  Lemma forest_rebuild_lt (X Y: Type) (i: nat)
        (ts1: list (bt X)) (ts2: list (bt Y)) (cs: list (bt nat)):
         ts1 ~lt ts2 -> @forest_rebuild X i ts1 cs = @forest_rebuild Y i ts2 cs.
  Proof.
    intros H; revert H i cs.
    induction 1 as [ | [|] [|] ? ? H1 ]; 
      intros ? cs; simpl; auto; try (inversion H1; fail).
    + f_equal; auto.
    + destruct cs as [ | ? [|] ]; simpl; auto; f_equal; auto.
  Qed.
     
  Variable (X : Type).
 
  Implicit Type (i: nat) (t : bt X) (l m ll ts : list (bt X)) (cs: list (bt nat)).

  Lemma forest_rebuild_spec i ts cs :
    subtrees ts ~lt cs
    -> is_bfn_from (length ts + i) cs (* skip over root labels *)
    -> ts ~lt forest_rebuild i ts cs /\ is_bfn_from i (forest_rebuild i ts cs).
  Proof.
    intros H1 H2.
    destruct (bfn_f i ts) as (ls & H3 & H4).
    generalize (forest_rebuild_lt i cs H3); intros H5.
    rewrite H5.
    assert (cs = subtrees ls) as E.
    { apply lbt_is_bfn_from_eq with (2 := H2).
      * apply lbt_eq_sym, lbt_eq_trans with (2 := H1),
              lbt_eq_sym, lbt_eq_subtrees; assumption.
      * red in H4.
        rewrite bft_f_fix_2 in H4.
        apply is_seq_from_app_right in H4.
        rewrite map_length, <- (Forall2_length H3) in H4; assumption. }
    rewrite E, forest_rebuild_id; try (split; assumption).
    red in H4.
    rewrite bft_f_fix_2 in H4.
    revert H4; apply is_seq_from_app_left.
  Qed.

  Definition bfn_level_f i l : { r | l ~lt r /\ is_bfn_from i r }.
  Proof.
    induction on i l as loop with measure (lsum l).
    case_eq l.
    + intros E.
      exists nil; split.
      * constructor.
      * red; rewrite bft_f_fix_0; red; auto.
    + intros b l' E.
      case_eq (forest_children l).
      intros n cs E'.
      refine (let (r',Hr') := loop (n+i) cs _ in _).
      { rewrite forest_children_eq in E'; inversion E'.
        destruct (subtrees_dec l); auto; subst; discriminate. }
      exists (forest_rebuild i l r').
      rewrite forest_children_eq in E'; inversion E'; subst n cs.
      destruct Hr'; rewrite <- E; apply forest_rebuild_spec; assumption.
    Defined.

    Let bfn_level_full t : { t' | t ~t t' /\ is_seq_from 1 (bft_forest t') }.
    Proof.
      refine (let (r,Hr) := bfn_level_f 1 (t::nil) in _).
      destruct r as [ | t' r ].
      + exfalso; destruct Hr as (Hr & _); inversion Hr.
      + exists t'.
        destruct Hr as (H1 & H2).
        apply Forall2_cons_inv in H1.
        destruct H1 as (H1 & H3).
        inversion H3; subst r.
        split; assumption.
    Qed.

    Definition bfn_level t := proj1_sig (bfn_level_full t).

    Fact bfn_level_spec_1 t : t ~t bfn_level t.
    Proof. apply (proj2_sig (bfn_level_full t)). Qed.
 
    Fact bfn_level_spec_2 t : is_seq_from 1 (bft_forest (bfn_level t)).
    Proof. apply (proj2_sig (bfn_level_full t)). Qed.
 
    Corollary bfn_level_spec_3 t : bft_std (bfn_level t) = seq_an 1 (m_bt t).
    Proof.
      generalize (bfn_level_spec_2 t).
      rewrite is_seq_from_spec.
      rewrite bft_forest_eq_bft_std.
      rewrite bft_std_length.
      rewrite (bt_eq_m (bfn_level_spec_1 t)).
      trivial.
    Qed.

End breadth_first_numbering_by_levels.

(*
Check bfn_level_spec_1.
Check bfn_level_spec_3.
*)