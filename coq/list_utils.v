(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega Permutation.

Set Implicit Arguments.

Infix "~p" := (@Permutation _) (at level 80, no associativity).

Section map.

  Variables (X Y : Type) (f g : X -> Y).

  Fact map_ext_dep l : (forall x, In x l -> f x = g x) -> map f l = map g l.
  Proof. rewrite <- Forall_forall; induction 1; simpl; f_equal; auto. Qed.

  Fact map_ext : (forall x, f x = g x) -> (forall l, map f l = map g l).
  Proof. intros; apply map_ext_dep; auto. Qed.

End map.

Definition list_length_split X n (ll : list X) : 
    { l : _ & { r | ll = l++r /\ length l = n } } + { length ll < n }.
Proof.
  revert ll; induction n as [ | n IHn ].
  + left; exists nil, ll; auto.
  + intros [ | x ll ].
    * right; simpl; omega.
    * destruct (IHn ll) as [ (l & r & H1 & H2) | H1 ].
      - left; exists (x::l), r; split; subst; auto.
      - right; simpl; omega.
Qed.

Definition list_length_prefix X n (ll : list X) : 
    n <= length ll -> { l : _ & { r | ll = l++r /\ length l = n } }.
Proof. intro; destruct (list_length_split n ll); trivial; omega. Qed.

Section list_length_eq_ind.

  Variable (X : Type) (P : list X -> list X -> Prop)
           (HP0 : P nil nil)
           (HP1 : forall x y l m, length l = length m -> P l m -> P (x::l) (y::m)).

  Theorem list_length_eq_ind l m : length l = length m -> P l m.
  Proof.
    intros H; cut (Forall2 (fun _ _ => True) l m).
    + induction 1; auto.
    + revert m H; induction l; intros [|]; auto; discriminate.
  Qed.

End list_length_eq_ind.

Section app.

  Variable X : Type.

  Fact split_In ll l (x : X) r : ll = l++x::r -> In x ll.
  Proof. intros; subst; apply in_or_app; simpl; auto. Qed.

  Fact in_concat_iff ll (x : X) : In x (concat ll) <-> exists l, In x l /\ In l ll.
  Proof.
    split.
    * induction ll as [ | l ll IH ]; simpl.
      - intros [].
      - intros H; apply in_app_or in H.
        destruct H as [ H | H ].
        + exists l; split; auto.
        + destruct IH as (l1 & ? & ?); auto; exists l1; auto.
   * intros (l & H1 & H2).
     apply in_split in H2.
     destruct H2 as (ll1 & ll2 & ?); subst.
     rewrite concat_app; apply in_or_app; simpl; right.
     apply in_or_app; simpl; auto.
  Qed.

End app.

Section list_sum.

  Definition list_sum := fold_right plus 0.

  Fact list_sum_app l m : list_sum (l++m) = list_sum l + list_sum m.
  Proof. induction l as [ | x l IHl ]; simpl; auto; rewrite IHl; omega. Qed.

  Fact length_concat X ll : length (concat ll) = list_sum (map (@length X) ll).
  Proof. induction ll; simpl; auto; rewrite app_length; f_equal; trivial. Qed.

End list_sum.

Section incl.

  Variable X : Type.
  
  Implicit Type l : list X.
  
  Fact incl_cons_linv l m x : incl (x::m) l -> In x l /\ incl m l.
  Proof.
    intros H; split.
    + apply H; left; auto.
    + intros ? ?; apply H; right; auto.
  Qed.

  Fact incl_app_rinv l m p : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
  Proof.
    induction m as [ | x m IHm ].
    + exists nil, nil; simpl; repeat split; auto; intros ? [].
    + intros H.
      apply incl_cons_linv in H.
      destruct H as (H1 & H2).
      destruct (IHm H2) as (m1 & m2 & H3 & H4 & H5).
      apply in_app_or in H1; destruct H1.
      * exists (x::m1), m2; repeat split; auto.
        - constructor 2; auto.
        - intros ? [|]; subst; auto.
      * exists m1, (x::m2); repeat split; auto.
        - apply Permutation_cons_app; auto.
        - intros ? [|]; subst; auto.
  Qed.
  
  Fact incl_cons_rinv x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ Forall (eq x) m1 /\ incl m2 l.
  Proof.
    intros H.
    apply (@incl_app_rinv (x::nil) _ l) in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    exists m1, m2; repeat split; auto.
    rewrite Forall_forall.
    intros a Ha; apply H2 in Ha; destruct Ha as [ | [] ]; auto.
  Qed.

  Fact incl_right_cons_choose x l m : incl m (x::l) -> In x m \/ incl m l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
    destruct m1 as [ | y m1 ].
    + right.
      intros u H; apply H3; revert H.
      apply Permutation_in; auto.
    + left.
      apply Permutation_in with (1 := Permutation_sym H1).
      rewrite Forall_forall in H2.
      rewrite (H2 y); left; auto.
  Qed.

  Fact incl_left_right_cons x l y m : incl (x::l) (y::m) -> y = x  /\ In y l 
                                                         \/ y = x  /\ incl l m
                                                         \/ In x m /\ incl l (y::m).
  Proof.
    intros H; apply incl_cons_linv in H.
    destruct H as [ [|] H2 ]; auto.
    apply incl_right_cons_choose in H2; tauto.
  Qed.

  Fact perm_incl_left m1 m2 l: m1 ~p m2 -> incl m2 l -> incl m1 l.
  Proof. intros H1 H2 ? H. apply H2; revert H; apply Permutation_in; auto. Qed.

  Fact perm_incl_right m l1 l2: l1 ~p l2 -> incl m l1 -> incl m l2.
  Proof.
    intros H1 H2 ? ?; apply Permutation_in with (1 := H1), H2; auto.
  Qed.
  
End incl.

Section Permutation_tools.

  Variable X : Type.
  
  Implicit Types (l : list X).
  
  Theorem Permutation_In_inv l1 l2: l1 ~p l2 -> forall x, In x l1 -> exists l, exists r, l2 = l++x::r.
  Proof. intros H ? ?; apply in_split, Permutation_in with (1 := H); auto. Qed.
  
  Fact perm_in_head x l : In x l -> exists m, l ~p x::m.
  Proof.
    induction l as [ | y l IHl ].
    + destruct 1.
    + intros [ ? | H ]; subst.
      * exists l; apply Permutation_refl.
      * destruct (IHl H) as (m & Hm).
        exists (y::m).
        apply Permutation_trans with (2 := perm_swap _ _ _).
        constructor 2; auto.
  Qed.

End Permutation_tools.

Section Forall.

  Variable (X : Type) (R : X -> Prop).

  Fact Forall_app l m : Forall R l -> Forall R m -> Forall R (l++m).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall_map Y f l : Forall (fun y : Y => R (f y)) l -> Forall R (map f l).
  Proof. induction 1; constructor; auto. Qed.

End Forall.

Section Forall2.

  Variables (X Y : Type) (R : X -> Y -> Prop).

  Fact Forall2_length l m : Forall2 R l m -> length l = length m.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact Forall2_nil_inv_right l : Forall2 R nil l -> l = nil.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_cons_inv x l y m : Forall2 R (x::l) (y::m) -> R x y /\ Forall2 R l m.
  Proof. inversion 1; auto. Qed.

  Fact Forall2_rev l m : Forall2 R l m -> Forall2 R (rev l) (rev m).
  Proof. induction 1; simpl; auto; apply Forall2_app; simpl; auto. Qed.

  Fact Forall2_rev_eq l m : Forall2 R l m <-> Forall2 R (rev l) (rev m).
  Proof.
    split.
    + apply Forall2_rev.
    + intros H.
      rewrite <- (rev_involutive l),  <- (rev_involutive m).
      apply Forall2_rev; trivial.
  Qed.
 
  Fact Forall2_app_inv l1 l2 m1 m2 : length l1 = length m1
                                  -> Forall2 R (l1++l2) (m1++m2)
                                  -> Forall2 R l1 m1 /\ Forall2 R l2 m2.
  Proof.
    revert m1; induction l1 as [ | x l1 IH ]; intros [ | y m1 ]; 
      try discriminate; simpl; intros H1 H2; auto.
    apply Forall2_cons_inv in H2.
    destruct H2; destruct (IH m1); auto.
  Qed.

  Fact Forall2_snoc_inv l x m y : Forall2 R (l++x::nil) (m++y::nil) -> R x y /\ Forall2 R l m.
  Proof.
    intros H.
    apply Forall2_rev in H.
    rewrite rev_app_distr, rev_app_distr in H; simpl in H.
    apply Forall2_cons_inv in H; destruct H as [ H1 H ]; split; auto.
    rewrite <- (rev_involutive l), <- (rev_involutive m); apply Forall2_rev; auto.
  Qed.

  Fact Forall2_2snoc_inv l a b m u v : Forall2 R (l++a::b::nil) (m++u::v::nil) 
                                    -> R a u /\ R b v /\ Forall2 R l m.
  Proof.
    replace (l++a::b::nil) with ((l++a::nil)++b::nil) by (rewrite app_ass; auto).
    replace (m++u::v::nil) with ((m++u::nil)++v::nil) by (rewrite app_ass; auto).
    intros H.
    apply Forall2_snoc_inv in H; destruct H as (H1 & H).
    apply Forall2_snoc_inv in H; tauto.
  Qed.

  Hint Resolve Forall2_app.

  Fact Forall2_concat l m : Forall2 (Forall2 R) l m -> Forall2 R (concat l) (concat m).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall2_sym l m : Forall2 R l m -> Forall2 (fun y x => R x y) m l.
  Proof. induction 1; constructor; auto. Qed.
  
  Fact Forall2_In_inv_left l m x : Forall2 R l m -> In x l -> exists y, In y m /\ R x y.
  Proof. induction 1; intros []; subst; firstorder. Qed.    

End Forall2.

Hint Resolve Forall2_app.

Tactic Notation "Forall2" "inv" hyp(H) "as" ident(E) :=
  match type of H with
    | Forall2 _ nil _ => apply Forall2_nil_inv_right in H; rename H into E
    | Forall2 _ (_::_) (_::_) => apply Forall2_cons_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_::nil) (_++_::nil) => apply Forall2_snoc_inv in H; destruct H as [ E H ]
    | Forall2 _ (_++_) (_++_) => apply Forall2_app_inv in H; [ destruct H as [ E H ] | ]
  end.

Fact Forall2_map_left X Y Z (f : X -> Y) (R : Y -> Z -> Prop) l m : 
     Forall2 (fun x z => R (f x) z) l m -> Forall2 R (map f l) m.
Proof. induction 1; simpl; auto. Qed.

Fact Forall2_mono X Y (R S : X -> Y -> Prop) l m : 
        (forall x y, R x y -> S x y)
     -> Forall2 R l m -> Forall2 S l m.
Proof. induction 2; auto. Qed.

Section seq_an.

  (* seq_an a n = [a;a+1;...;a+(n-1)] *)

  Fixpoint seq_an a n: list nat :=
    match n with
      | 0    => nil
      | S n  => a::seq_an (S a) n
    end.

  Fact seq_an_length a n : length (seq_an a n) = n.
  Proof. revert a; induction n; simpl; intros; f_equal; auto. Qed.

  Fact seq_an_spec a n x : In x (seq_an a n) <-> a <= x < a+n.
  Proof. 
    revert x a; induction n as [ | n IHn ]; intros x a; simpl;
      [ | rewrite IHn ]; omega.
  Qed.

  Fixpoint is_seq_from n (l : list nat) { struct l }: Prop :=
    match l with  
      | nil  => True
      | x::l => n=x /\ is_seq_from (S n) l
    end.

  Fact is_seq_from_app_left n l m : is_seq_from n (l++m) -> is_seq_from n l.
  Proof.
    revert n.
    induction l as [ | x l IH ]; intros n; simpl; auto.
    intros []; subst; auto.
  Qed.

  Fact is_seq_from_app_right n l m : is_seq_from n (l++m) -> is_seq_from (length l+n) m.
  Proof.
    revert n.
    induction l as [ | x l IH ]; intros n; simpl; auto.
    intros []; subst.
    replace (S (length l+x)) with (length l+S x) by omega; auto.
  Qed.

  Theorem is_seq_from_spec a l : is_seq_from a l <-> l = seq_an a (length l).
  Proof.
    revert a; induction l as [ | x l IH ]; intros a; simpl.
    + split; auto.
    + rewrite IH; split.
      * intros []; subst; f_equal; auto.
      * injection 1; auto.
  Qed.

End seq_an.


