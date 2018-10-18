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

(** Binary trees *)

Require Import Arith Omega List Relations.

Require Import list_utils.

Set Implicit Arguments.

Section bt.

  Variable X : Type.

  Inductive bt := leaf : X -> bt | node : bt -> X -> bt -> bt.

  Definition root (t : bt) : X :=
    match t with 
      | leaf x     => x
      | node _ x _ => x
    end.

  Definition subt (t : bt) : list bt :=
    match t with 
      | leaf x     => nil
      | node a _ b => a::b::nil 
    end.

  (** measure: number of constructors *)

  Fixpoint m_bt (t: bt): nat :=
    match t with 
      | leaf _     => 1
      | node a _ b => 1 + m_bt a + m_bt b
    end.

  Fact m_bt_ge_1 t : 1 <= m_bt t.
  Proof. destruct t; simpl; omega. Qed.

  (* The measure of the size of a forest on which most complicated inductions are based *) 

  Definition lsum := fold_right (fun t y => m_bt t + y) 0.

  Fact lsum_app l m : lsum (l++m) = lsum l + lsum m.
  Proof. induction l; simpl; omega. Qed.

  Notation roots := (map root).
  Notation subtrees := (flat_map subt).

  Fact roots_app l m : roots (l++m) = roots l ++ roots m.
  Proof. apply map_app. Qed. 
  
  Fact subtrees_app l m : subtrees (l++m) = subtrees l ++ subtrees m.
  Proof.
    repeat rewrite flat_map_concat_map.
    rewrite map_app, concat_app; trivial.
  Qed. 

  Fact subtrees_dec ll : ll = nil \/ lsum (subtrees ll) < lsum ll.
  Proof.
    induction ll as [ | [|] ]; simpl; auto;
      right; destruct IHll; subst; simpl; auto; omega.
  Qed.

  Fact subtrees_le ll : lsum (subtrees ll) <= lsum ll.
  Proof. destruct (subtrees_dec ll); subst; simpl; omega. Qed.

  Fact lsum_roots_subtrees ll : lsum ll = length (roots ll) + lsum (subtrees ll).
  Proof.
    induction ll as [ | [|] ]; simpl; omega.
  Qed.

  (* A branch is a list of left/right Boolean choices *)

  (* The branches that correspond to a node in a binary tree *)

  (** [false] for the left subtree, [true] for the right subtree *)

  Inductive btb : bt -> list bool -> Prop :=
    | in_btb_0 : forall t, btb t nil
    | in_btb_1 : forall l u x v, btb u l -> btb (node u x v) (false::l) 
    | in_btb_2 : forall l u x v, btb v l -> btb (node u x v) (true::l).

  Hint Constructors btb.

  Fact btb_inv_1 l u x v : btb (node u x v) (false::l) -> btb u l.
  Proof. inversion 1; trivial. Defined.

  Fact btb_inv_2 l u x v : btb (node u x v) (true::l) -> btb v l.
  Proof. inversion 1; trivial. Defined.

  (* The partial functional map from a branch to the value of that node *)

  Inductive bt_path_node : bt -> list bool -> X -> Prop :=
    | in_bpn_0 : forall t, bt_path_node t nil (root t)
    | in_bpn_1 : forall l u x v r, bt_path_node u l r -> bt_path_node (node u x v) (false::l) r
    | in_bpn_2 : forall l u x v r, bt_path_node v l r -> bt_path_node (node u x v) (true::l) r.

  Fact bt_path_node_fun t l x y :  bt_path_node t l x ->  bt_path_node t l y -> x = y.
  Proof. induction 1; inversion 1; auto. Qed.

  (* A branch has a value through bt_path_node iff it is a branch of the tree *)

  Fact btb_spec (l: list bool) (t: bt) : btb t l <-> exists (x: X), bt_path_node t l x.
  Proof.
    split.
    + induction 1 as [ t | l u x v _ (y & Hy) | l u x v _ (y & Hy) ].
      * exists (root t); constructor.
      * exists y; constructor; auto.
      * exists y; constructor; auto.
    + intros (r & H); revert H.
      induction 1; constructor; auto.
  Qed.

End bt.

Arguments root {X}.
Arguments m_bt {X}.

Notation roots := (map (@root _)).
Notation subtrees := (flat_map (@subt _)).


Hint Constructors btb.

Section branch_orders.

  (** We define two total and decidable strict orders on branches
        <l : for lexicographic order corresponding to DFT
        <b : for length then lexico corresponding to BFT

    *)

  Reserved Notation "x '<l' y" (at level 70, no associativity).
  Reserved Notation "x '<b' y" (at level 70, no associativity).

  (* The Depth First Traversal order between bt branches 

     The order is the lexicographic product where left (false)
     is less than right (true)

   *)

  Inductive lb_lex : list bool -> list bool -> Prop :=
    | in_lb_0 : forall b l, nil <l b::l
    | in_lb_1 : forall l m, false::l <l true::m
    | in_lb_2 : forall b l m, l <l m -> b::l <l b::m
  where "x <l y" := (lb_lex x y).

  Hint Constructors lb_lex.
  Fact lb_lex_irrefl (l: list bool) : ~ l <l l.
  Proof. 
    assert (forall l m, l <l m -> l <> m) as H.
    { induction 1; try discriminate; inversion 1; tauto. }
    intros H1; apply (H _ _ H1); reflexivity.
  Qed.

  Fact lb_lex_trans (l m k: list bool) : l <l m -> m <l k -> l <l k.
  Proof.
    intros H; revert H k.
    induction 1; inversion 1; constructor; auto.
  Qed.

  Fact lb_lex_inv (x: bool) (l m: list bool) : x::l <l x::m -> l <l m.
  Proof. inversion 1; auto. Qed.

  Fact lb_lex_mono (x: bool) (l m: list bool) : l <l m <-> x::l <l x::m.
  Proof. split; auto; apply lb_lex_inv. Qed.

  Fact lb_lex_nil (x: bool) (m: list bool) : nil <l x::m.
  Proof. constructor. Qed.

  Fact lb_lex_cons (l m: list bool) : false::l <l true::m.
  Proof. constructor. Qed.

  Definition lb_lex_dec (l m: list bool) : { l <l m } + { l = m } + { m <l l }.
  Proof.
    revert m; induction l as [ | [] l IHl ]; intros [ | [] m ].
    + tauto.
    + do 2 left; constructor.
    + do 2 left; constructor.
    + right; constructor.
    + destruct (IHl m) as [ [ ? | ? ] | ? ].
      * do 2 left; constructor; auto.
      * subst; left; right; auto.
      * right; constructor; auto.  
    + right; constructor.
    + right; constructor.
    + do 2 left; constructor.
    + destruct (IHl m) as [ [ ? | ? ] | ? ].
      * do 2 left; constructor; auto.
      * subst; left; right; auto.
      * right; constructor; auto.
   Qed.

  (* The Breadth First Traversal order between bt branches 

     Shorter branches are first and two branches of the 
     same length are sorted lexicographically 
 
   *)

  Definition bft_order (l m: list bool) : Prop :=
    length l < length m \/ length l = length m /\ l <l m.

  Notation "l <b m" := (bft_order l m).

  Fact bft_order_irrefl (l: list bool) : ~ l <b l.
  Proof. 
    intros [ H | (_ & H) ]; revert H.
    + apply lt_irrefl.
    + apply lb_lex_irrefl.
  Qed.

  Fact bft_order_trans (l m k: list bool) : l <b m -> m <b k -> l <b k.
  Proof.
    intros [ | [] ] [ | [] ]; try (left; omega).
    right; split; try omega.
    apply lb_lex_trans with m; assumption.
  Qed.

  Fact bft_order_mono (x: bool) (l m: list bool) : l <b m <-> x::l <b x::m.
  Proof.
    split.
    + intros [ H | (H1 & H2) ].
      * left; simpl; omega.
      * right; split; simpl; auto.
    + intros [ H | (H1 & H2) ].
      * left; simpl in *; omega.
      * right; split; simpl in *; try omega.
        revert H2; apply lb_lex_inv.
  Qed.

  Fact bft_order_lt (m1 m2: list bool) : length m1 < length m2 -> m1 <b m2.
  Proof. left; auto. Qed.

  Fact bft_order_eq (m1 m2: list bool) : length m1 = length m2 -> false::m1 <b true::m2.
  Proof. right; simpl; split; auto. Qed.

  Definition bft_order_dec (l m: list bool) : { l <b m } + { l = m } + { m <b l }.
  Proof.
    destruct (le_lt_dec (length l) (length m)).
    2: right; left; auto.
    destruct (le_lt_dec (length m) (length l)).
    2: do 3 left; auto.
    destruct (lb_lex_dec l m) as [[|]|].
    + do 2 left; right; split; auto; omega.
    + tauto.
    + do 2 right; split; auto; omega.
  Qed.

End branch_orders.

Definition is_dft_order (R: relation (list bool)): Prop :=
            (forall l, ~ R l l)
          /\ transitive _ R
          /\ (forall x l m, R l m <-> R (x::l) (x::m))
          /\ (forall x m, R nil (x::m))
          /\ (forall m1 m2, R (false::m1) (true::m2)).

Section dft_order_characterization.

  (* dft_order (ie lb_lex) satisfies and is characterized by the following axioms *)

  Hint Resolve lb_lex_irrefl lb_lex_trans lb_lex_mono lb_lex_nil lb_lex_cons.

  Theorem lb_lex_is_dft_order : is_dft_order lb_lex.
  Proof. repeat (split; auto); red; apply lb_lex_trans. Qed.

  Variables (R : relation (list bool)) (HR : is_dft_order R).
      
  Let R_irrefl : forall l, ~ R l l.
  Proof. apply HR. Qed.
  Let R_trans : transitive _ R.
  Proof. apply HR. Qed.
  Let R_mono : forall x l m, R l m <-> R (x::l) (x::m).
  Proof. apply HR. Qed.
  Let R_nil : forall x m, R nil (x::m).
  Proof. apply HR. Qed.
  Let R_cons : forall m1 m2, R (false::m1) (true::m2).
  Proof. apply HR. Qed.

  Hint Constructors lb_lex.

  Let HR3 x m : ~ R (x::m) nil.
  Proof. 
    intros H; apply (@R_irrefl nil).
    revert H; apply R_trans, R_nil.
  Qed. 

  Let HR4 m1 m2 : ~ R (true::m1) (false::m2).
  Proof. 
    intros H; apply (@R_irrefl (false::m2)).
    revert H; apply R_trans, R_cons.
  Qed. 

  Theorem dft_order_charac l m : R l m <-> lb_lex l m.
  Proof.
    split.
    + revert m; induction l as [ | x l ]; intros [ | y m ]; auto.
      * intros H; apply R_irrefl in H; tauto.
      * intros H; apply HR3 in H; tauto.
      * destruct x; destruct y; intros H; auto.
        - apply R_mono in H; constructor; auto.
        - apply HR4 in H; tauto.
        - apply R_mono in H; constructor; auto. 
    + induction 1; auto; apply R_mono; auto.
  Qed.

End dft_order_characterization.

Definition is_bft_order (R: relation (list bool)): Prop :=
            (forall l, ~ R l l)
          /\ transitive _ R
          /\ (forall x l m, R l m <-> R (x::l) (x::m))
          /\ (forall m1 m2, length m1 < length m2 -> R m1 m2)
          /\ (forall m1 m2, length m1 = length m2 -> R (false::m1) (true::m2)).

Section bft_order.

  (* bft_order satisfies and is characterized by the following axioms *)

  Hint Resolve bft_order_irrefl bft_order_trans bft_order_mono bft_order_lt bft_order_eq.

  Theorem bft_order_checks : is_bft_order bft_order.
  Proof. repeat (split; auto); red; apply bft_order_trans. Qed.

  Variables (R : relation (list bool)) (HR : is_bft_order R).

  Let R_irrefl : forall l, ~ R l l.
  Proof. apply HR. Qed.
  Let R_trans : transitive _ R.
  Proof. apply HR. Qed.
  Let R_mono : forall x l m, R l m <-> R (x::l) (x::m).
  Proof. apply HR. Qed.
  Let R_lt : forall m1 m2, length m1 < length m2 -> R m1 m2.
  Proof. apply HR. Qed.
  Let R_eq : forall m1 m2, length m1 = length m2 -> R (false::m1) (true::m2).
  Proof. apply HR. Qed.

  Let HR3 m1 m2 : length m2 < length m1 -> ~ R m1 m2.
  Proof. 
    intros H1 H2.
    apply (@R_irrefl m2); revert H2.
    apply R_trans, R_lt; auto.
  Qed.

  Let HR4 m1 m2 : length m1 = length m2 -> ~ R (true::m1) (false::m2).
  Proof. 
    intros H1 H2; apply (@R_irrefl (false::m2)).
    revert H2; apply R_trans, R_eq; omega.
  Qed. 

  Theorem bft_order_charac l m : R l m <-> bft_order l m.
  Proof.
    split.
    + destruct (lt_eq_lt_dec (length l) (length m)) as [ [ H | H ] | H ].
      all: cycle 2.
      { intros E; apply HR3 in E; tauto. }
      { intros; apply bft_order_lt; assumption. }
      pattern l, m.
      revert l m H; apply list_length_eq_ind.
      * intros H; apply R_irrefl in H; tauto.
      * intros [|] [|] l m H1 IH H2.
        - revert H2; rewrite <- bft_order_mono, <- R_mono; auto.
        - apply HR4 in H2; tauto.
        - apply bft_order_eq; assumption.
        - revert H2; rewrite <- bft_order_mono, <- R_mono; auto.
    + intros [ H | [ H1 H2 ] ].
      * apply R_lt; assumption.
      * revert H1; induction H2.
        - intros; discriminate.
        - simpl; intros; apply R_eq; omega.
        - simpl; intros; apply R_mono; auto.
  Qed.

End bft_order.

(** Equivalence between trees and forests, same structure,
    only the values of nodes differ *)

Reserved Notation "x '~t' y" (at level 70, no associativity).
Reserved Notation "x '~lt' y" (at level 70, no associativity).

Section bt_eq.

  Variable (X Y : Type).

  Inductive bt_eq : bt X -> bt Y -> Prop :=
    | in_bt_eq_0 : forall x y, leaf x ~t leaf y
    | in_bt_eq_1 : forall x a b y c d, a ~t c -> b ~t d -> node a x b ~t node c y d
  where "x ~t y" := (bt_eq x y).

  Fact bt_eq_m (t1: bt X) (t2: bt Y) : t1 ~t t2 -> m_bt t1 = m_bt t2.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact bt_eq_node_inv a x b c y d : node a x b ~t node c y d -> a ~t c /\ b ~t d.
  Proof. inversion 1; auto. Qed.

End bt_eq.

Arguments bt_eq {X Y}.

Notation "x ~t y" := (bt_eq x y).
Notation "l ~lt m" := (Forall2 bt_eq l m). (** extension to forests *)

Hint Constructors bt_eq.

Fact bt_eq_refl X (t : bt X) : t ~t t.
Proof. induction t; constructor; auto. Qed.

Fact bt_eq_sym X Y (s : bt X) (t : bt Y) : s ~t t -> t ~t s.
Proof. induction 1; constructor; auto. Qed.

Fact bt_eq_trans X Y Z (r : bt X) (s : bt Y) (t : bt Z) : r ~t s -> s ~t t -> r ~t t.
Proof. intros H; revert H t; induction 1; inversion 1; auto. Qed.

Fact lbt_eq_refl X (l : list (bt X)) : l ~lt l.
Proof. induction l; constructor; auto; apply bt_eq_refl. Qed.

Fact lbt_eq_sym X Y (s : list (bt X)) (t : list (bt Y)) : s ~lt t -> t ~lt s.
Proof. induction 1; constructor; auto; apply bt_eq_sym; auto. Qed.

Fact lbt_eq_trans X Y Z (r : list (bt X)) (s : list (bt Y)) (t : list (bt Z)) : r ~lt s -> s ~lt t -> r ~lt t.
Proof.
  intros H; revert H t.
  induction 1 as [ | a b r s H1 H2 IH2 ]; intros [ | c t ] H3; try (inversion H3; fail).
  + constructor.
  + apply Forall2_cons_inv in H3.
    destruct H3 as (H3 & H4).
    constructor; auto.
    apply bt_eq_trans with (1 := H1); auto.
Qed. 

Fact lbt_eq_lsum  X Y (s : list (bt X)) (t : list (bt Y)) : s ~lt t -> lsum s = lsum t.
Proof.
  induction 1 as [ | x y s t H1 H2 IH2 ]; simpl; auto.
  apply bt_eq_m in H1; omega.
Qed.

Fact lbt_eq_subtrees X Y (s : list (bt X)) (t : list (bt Y)) : s ~lt t -> subtrees s ~lt subtrees t.
Proof.
  induction 1 as [ | x y s t H1 H2 IH2 ]; simpl.
  + constructor.
  + apply Forall2_app; auto.
    destruct x as [|]; destruct y as [|]; 
      inversion H1; subst; simpl; repeat constructor; auto.
Qed.
