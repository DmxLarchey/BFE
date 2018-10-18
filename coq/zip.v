(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import list_utils.

Set Implicit Arguments.

Section zip.

  Variable (X : Type) (f : X -> X -> X).

  Fixpoint zip l m : list X :=
    match l, m with
      | nil,  _    => m
      | _,    nil  => l
      | x::l, y::m => f x y :: zip l m
    end.

  Fact zip_fix_1 l : zip l nil = l.
  Proof. destruct l; auto. Qed.

  Fact zip_app l1 l2 m1 m2 : length l1 = length m1 -> zip (l1++l2) (m1++m2) = zip l1 m1 ++ zip l2 m2.
  Proof.
    revert m1; induction l1 as [| ? ? IH]; intros [|]; simpl; auto; try discriminate; intros; f_equal; apply IH; omega.
  Qed.

  Fact zip_app_left_le l1 l2 m x : length m <= length l1 -> In x l2 -> In x (zip (l1++l2) m).
  Proof.
    revert m; induction l1 as [ | y l1 IH ]; intros [ | z m ]; simpl; try omega.
    + rewrite zip_fix_1; auto.
    + right; apply in_or_app; simpl; auto.
    + right; apply IH; auto; omega.
  Qed.

  Fact zip_app_left l1 l2 m x : length m < length l1 -> In x l2 -> In x (zip (l1++l2) m).
  Proof. intros; apply zip_app_left_le; auto; omega. Qed.
  
  Fact zip_app_right_le l m1 m2 x : length l <= length m1 -> In x m2 -> In x (zip l (m1++m2)).
  Proof.
    revert m1; induction l as [ | y l IH ]; intros [ | z m1 ]; simpl; auto; try omega.
    + right; apply in_or_app; simpl; auto.
    + right; apply IH; auto; omega.
  Qed.

  Fact zip_app_right l m1 m2 x : length l < length m1 -> In x m2 -> In x (zip l (m1++m2)).
  Proof. intros; apply zip_app_right_le; auto; omega. Qed.
 
  Fact zip_spec l m c : In c (zip l m) <-> (exists m1 m2, length l <= length m1 /\ m = m1++c::m2)
                                        \/ (exists l1 l2, length m <= length l1 /\ l = l1++c::l2)
                                        \/ (exists l1 x l2 m1 y m2, c = f x y /\ l = l1++x::l2 
                                                       /\ m = m1++y::m2 /\ length l1 = length m1). 
  Proof.
    split.
    + revert m; induction l as [ | x l IHl ]; simpl; intros m H.
      * apply in_split in H; destruct H as (m1 & m2 & ?); subst.
        left; exists m1, m2; split; auto; omega.
      * destruct m as [ | y m ]; destruct H as [ H | H ].
        - right; left; subst; exists nil, l; auto.
        - apply in_split in H; destruct H as (l1 & l2 & ?); subst.
          right; left; exists (x::l1), l2; split; auto; simpl; omega.
        - subst; right; right; exists nil, x, l, nil, y, m; simpl; auto.
        - destruct (IHl _ H) as [ (m1 & m2 & H1 & H2) 
                              | [ (l1 & l2 & H1 & H2) 
                                | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ]; clear H IHl.
          ++ left; subst; exists (y::m1), m2; simpl; split; auto; omega.
          ++ right; left; subst; exists (x::l1), l2; simpl; split; auto; omega.
          ++ right; right; subst; exists (x::l1), a, l2, (y::m1), b, m2; simpl; auto.
    + intros [ (m1 & m2 & H1 & H2) 
           | [ (l1 & l2 & H1 & H2) 
             | (l1 & a & l2 & m1 & b & m2 & H1 & H2 & H3 & H4) ] ]; subst.
      * revert m1 H1; induction l as [ | x l IHl ]; simpl; intros m H1.
        - apply in_or_app; simpl; auto.
        - destruct m; simpl in H1 |- *; try omega.
          right; apply IHl; omega.
      * revert l1 H1; induction m as [ | y m IHm ]; simpl; intros l H1.
        - rewrite zip_fix_1; apply in_or_app; simpl; auto.
        - destruct l; simpl in H1 |- *; try omega.
          right; apply IHm; omega.
      * revert m1 H4; induction l1; simpl; intros [] H1; simpl; try discriminate; auto.
  Qed.

  Variable (P : X -> Prop).

  Fact zip_monotone l m : Forall P l -> Forall P m -> (forall x y, In x l -> In y m -> P (f x y)) -> Forall P (zip l m).
  Proof. intros H; revert H m; do 2 (induction 1; simpl; auto). Qed.

End zip.

Section map_concat_zip.

  Variable (X Y : Type) (f : X -> Y) (g : X -> X -> X) (h : Y -> Y -> Y).

  (** the following expresses naturality of the monad multiplication [concat]: *)

  Fact map_concat ll : map f (concat ll) = concat (map (map f) ll).
  Proof. 
    induction ll; simpl; f_equal; auto.
    rewrite map_app; f_equal; auto.
  Qed.

  Hypothesis Hgh : forall x y, f (g x y) = h (f x) (f y). 

  (** [f] is a "morphism" from [g] to [h]: *)

  Fact map_zip l m : map f (zip g l m) = zip h (map f l) (map f m).
  Proof. revert m; induction l; intros [|]; simpl; f_equal; auto. Qed.

End map_concat_zip.

Fact map_zip_length X l m : map (@length X) (zip (@app _) l m) = zip plus (map (@length _) l) (map (@length _) m).
Proof.
  apply map_zip, app_length.
Qed.

Fact map_zip_app X Y (f : X -> Y) l m : 
    map (map f) (zip (@app _) l m) = zip (@app _) (map (map f) l) (map (map f) m).
Proof. apply map_zip; intros; apply map_app. Qed.

Fact zip_list_sum l m : list_sum (zip plus l m) = list_sum l + list_sum m.
Proof.
  revert m; induction l as [ | x l IHl ]; intros [|]; simpl; try omega.
  rewrite IHl; omega.
Qed.

Fact In_concat_zip_app_left X (x : X) ll mm : In x (concat ll) -> In x (concat (zip (@app _) ll mm)).
Proof.
  intros H; revert H mm.
  induction ll as [ | l ll IH ]; simpl.
  + intros [].
  + intros H; apply in_app_or in H.
    destruct H as [ H | H ].
    * intros []; simpl; try rewrite app_ass; apply in_or_app; tauto.
    * intros []; simpl; try rewrite app_ass; repeat (apply in_or_app; right; auto).
Qed.

Fact In_concat_zip_app_right X (x : X) ll mm : In x (concat mm) -> In x (concat (zip (@app _) ll mm)).
Proof.
  revert mm.
  induction ll as [ | l ll IH ]; simpl; auto.
  intros [ | m mm ]; simpl; intros H1; try tauto.
  rewrite app_ass; apply in_or_app; right.
  apply in_or_app.
  apply in_app_or in H1; firstorder.
Qed.

Fact Forall2_zip_app X Y R l1 m1 l2 m2 : 
       Forall2 (@Forall2 X Y R) l1 l2
    -> Forall2 (Forall2 R) m1 m2
    -> Forall2 (Forall2 R) (zip (@app _) l1 m1) (zip (@app _) l2 m2).
Proof. intros H; revert H m1 m2; do 2 (induction 1; simpl; auto). Qed.
