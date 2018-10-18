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

(** Extraction of a breadth-first traversal from Coq to Ocaml 

   open List;;

   type 'a bt = Leaf of 'a | Node of 'a bt * 'a * 'a bt;;

   let root t = match t with Leaf x -> x  | Node (_,x,_) -> x;;
   let subt t = match t with Leaf x -> [] | Node (a,x,b) -> [a;b];;

   (* forest_decomp ll = (map root ll, flat_map subt ll) *)

   let rec forest_decomp = function
     | []   -> ([], [])
     | t::l -> let ro,sf = forest_decomp l 
               in match t with
                    | Leaf x         -> (x::ro,sf)
                    | Node (a, x, b) -> (x::ro,a::b::sf)

   let rec bft_f = function 
     | [] -> []
     | _  -> let ro,st = forest_decomp u in ro @ bft_f st

   let bft_forest t = bft_f (t::nil)

*)

Require Import List Arith Omega Wellfounded Extraction.
Require Import list_utils wf_utils zip bt bft_std.

Set Implicit Arguments.

Section breadth_first_traversal.

  Context (X : Type).
 
  Implicit Type (t : bt X) (l m ll : list (bt X)).
  
  Fixpoint forest_decomp ll : list X * list (bt X) :=
    match ll with 
      | nil   => (nil,nil)
      | t::l => let (ro,sf) := forest_decomp l in
      match t with
        | leaf x     => (x::ro,sf)
        | node a x b => (x::ro,a::b::sf)
      end
    end.

  (** the following could have served as a less optimized definition *)
  Fact forest_decomp_eq ll : forest_decomp ll = (roots ll, subtrees ll).
  Proof. induction ll as [ | [] ? IH ]; simpl; auto; rewrite IH; auto. Qed.

  Section equivalences.
      
    Variable (bft_f : list (bt X) -> list X).

    Definition bft_f_prop_0 := forall l, bft_f l = roots l ++ bft_f (subtrees l).
    Definition bft_f_prop_1 := forall l m, bft_f (l++m) = roots l ++ bft_f (m++subtrees l).
    Definition bft_f_prop_2 := forall t l, bft_f (t::l) = root t :: bft_f (l++subt t).
    Definition bft_f_prop_3 := (forall x l, bft_f (leaf x::l) = x::bft_f l)
                     /\ (forall a b x l, bft_f (node a x b::l) = x::bft_f (l++a::b::nil)).

    (** The identity [bft_f (l++m) = roots l ++ bft_f (m++subtrees l)] is critical
        to show the correctness of Breadth First Numbering. *)

    (* The induction for the implications [bft_f_prop_0 -> bft_f_prop_1] and
       [bft_f_prop_2 -> bft_f_prop_1] is a bit complex because [l] and [m]
       alternate in the proof - we proceed by induction on [lsum (l++m)]. *)

    (** here is work to do: *)
    Let prop_0_prop_1 : bft_f_prop_0 -> bft_f_prop_1.
    Proof.
      unfold bft_f_prop_0, bft_f_prop_1.
      intros H l m.
      induction on l m as IH with measure (lsum (l++m)).
      destruct l as [ | t l ]; try (rewrite <- app_nil_end; auto; fail).
      rewrite H; simpl.
      rewrite (IH m), map_app, app_ass, app_ass, subtrees_app; auto.
      repeat rewrite lsum_app; simpl.
      generalize (subtrees_le l); destruct t; simpl; omega.
    Qed.

    (** the following just an instance relation: *)
    Let prop_1_prop_0 : bft_f_prop_1 -> bft_f_prop_0.
    Proof.
      unfold bft_f_prop_0, bft_f_prop_1.
      intros H l; rewrite (app_nil_end l) at 1.
      apply H.
    Qed.

    (** the following just an instance relation: *)
    Let prop_1_prop_2 : bft_f_prop_1 -> bft_f_prop_2.
    Proof.
      unfold bft_f_prop_1, bft_f_prop_2.
      intros H t l.
      specialize (H (t::nil) l).  
      simpl in H; rewrite H, <- app_nil_end; trivial.
    Qed.

    (** here is work to do: *)
    Let prop_2_prop_1 : bft_f_prop_2 -> bft_f_prop_1.
    Proof.
      unfold bft_f_prop_1, bft_f_prop_2.
      intros H l m.
      induction on l m as IH with measure (lsum (l++m)).
      destruct l as [ | t l ]; 
        try (rewrite <- app_nil_end; auto; fail).
      simpl; rewrite H; simpl; rewrite app_ass; f_equal.
      rewrite <- (app_ass m), <- IH; auto.
      simpl; repeat rewrite lsum_app.
      destruct t; simpl; omega.
    Qed.

    (** just two instances to look at: *)
    Let prop_2_prop_3 : bft_f_prop_2 -> bft_f_prop_3.
    Proof.
      unfold bft_f_prop_2, bft_f_prop_3.
      intros H; split.
      + intros ? ?; rewrite H.
        simpl; rewrite <- app_nil_end; auto.
      + intros; apply H.
    Qed.

    (** just a case analysis: *)
    Let prop_3_prop_2 : bft_f_prop_3 -> bft_f_prop_2.
    Proof.
      unfold bft_f_prop_2, bft_f_prop_3.
      intros [] [|] ?; simpl; auto.
      rewrite <- app_nil_end; auto.
    Qed.

    Theorem bft_f_equivalences :
           (bft_f_prop_0 -> bft_f_prop_1)
        /\ (bft_f_prop_1 -> bft_f_prop_2)
        /\ (bft_f_prop_2 -> bft_f_prop_3)
        /\ (bft_f_prop_3 -> bft_f_prop_0).
    Proof. repeat (split; auto). Qed.
  
  End equivalences.

  Section unicity.

    Variable (bf1 bf2 : list (bt X) -> list X).

    Hypothesis (H10 : bf1 nil = nil)
               (H20 : bf2 nil = nil)
               (H11: bft_f_prop_0 bf1)
               (H21: bft_f_prop_0 bf2).
            (* (H11 : forall l, bf1 l = roots l ++ bf1 (subtrees l))
               (H21 : forall l, bf2 l = roots l ++ bf2 (subtrees l)). *)

    Theorem bft_f_unicity l : bf1 l = bf2 l.
    Proof.
      induction on l as IH with measure (lsum l).
      case_eq l.
      + rewrite H10, H20; trivial.
      + intros b l' E; rewrite <- E, H11, H21.
        f_equal; apply IH.
        destruct (subtrees_dec l); auto.
        subst; discriminate.
    Qed.

  End unicity.

  Section existence.

    Ltac mysolve := try match goal with H: ?x <> ?x |- _ => destruct H; reflexivity end.

    (* we use the specification:
           
          bft_f nil = nil
          bft_f l = roots l ++ bft_f (subtrees l) for l <> nil

       let us first write the graph of the algorithm
     *)

    Inductive g_bft_f : list (bt X) -> list X -> Prop :=
      | in_g_bft_f_0 : g_bft_f nil nil
      | in_g_bft_f_1 : forall ll r, ll <> nil -> g_bft_f (subtrees ll) r -> g_bft_f ll (roots ll ++ r).

    (* This graph is functional *)

    Fact g_bft_f_fun ll r1 r2 : g_bft_f ll r1 -> g_bft_f ll r2 -> r1 = r2.
    Proof.
      intros H1; revert H1 r2.
      induction 1; inversion 1; subst; auto.
      mysolve.
      f_equal; auto.
    Qed.

    Fact g_bft_f_length ll r : g_bft_f ll r -> length r = lsum ll.
    Proof.
      induction 1 as [ | ll r H1 H2 IH2 ]; auto.
      rewrite app_length, IH2, <- lsum_roots_subtrees; auto.
    Qed.

    (* We define bft_f by measure induction on lsum l *)

    Let bft_f_rec l : sig (g_bft_f l).
    Proof.
      induction on l as loop with measure (lsum l).
      refine (match l as l' return l = l' -> sig (g_bft_f l) with
        | nil   => fun _  => exist _ nil _
        | t::l' => fun E1 => 
        match forest_decomp l as c return forest_decomp l = c -> sig (g_bft_f l) with
          | (ro,st) => fun E2 => let (mm,Hmm) := loop st _
                                 in exist _ (ro ++ mm) _ 
        end eq_refl
      end eq_refl).
      + subst; constructor.
      + rewrite forest_decomp_eq in E2; inversion E2.
        destruct (subtrees_dec l); auto; subst; discriminate.
      + rewrite forest_decomp_eq in E2; inversion E2.
        constructor; subst; auto; discriminate.
    Qed.

    Definition bft_f l := proj1_sig (bft_f_rec l).

    Fact bft_f_spec l : g_bft_f l (bft_f l).
    Proof. apply (proj2_sig _). Qed.

    Hint Resolve bft_f_spec.

    Fact bft_f_fix_0 : bft_f nil = nil.
    Proof. apply g_bft_f_fun with nil; auto; constructor. Qed.

    Fact bft_f_fix_1 ll : ll <> nil -> bft_f ll = roots ll ++ bft_f (subtrees ll).
    Proof. intro; apply g_bft_f_fun with ll; auto; constructor; auto. Qed.

    Hint Resolve bft_f_fix_1.

    Fact bft_f_fix_2: bft_f_prop_0 bft_f.
    (** for argument [lt], this is [bft_f lt = roots lt ++ bft_f (subtrees lt)]. *)
    Proof. 
      intro lt; destruct lt; auto.
      apply bft_f_fix_1; discriminate.
    Qed.

    Fact bft_f_length lt : length (bft_f lt) = lsum lt.
    Proof. apply g_bft_f_length, bft_f_spec. Qed.
 
  End existence.

  (* We derive additional properties from bft_f_fix_2 *)


  Hint Resolve bft_f_fix_2.

  Fact bft_f_fix_3: bft_f_prop_1 bft_f.
  (** for arguments [t l m], this is [bft_f (l++m) = roots l ++ bft_f (m++subtrees l)]. *)
  Proof. do 1 apply bft_f_equivalences; auto. Qed.

  Fact bft_f_fix_4: bft_f_prop_2 bft_f.
  (** for arguments [t l], this is [bft_f (t::l) = root t :: bft_f (l++subt t)]. *)
  Proof. do 2 apply bft_f_equivalences; auto. Qed.

  Fact bft_f_fix_oka_0 : bft_f nil = nil.
  Proof. apply bft_f_fix_0. Qed.

  Fact bft_f_fix_oka_1 x l : bft_f (leaf x::l) = x::bft_f l.
  Proof. do 3 apply bft_f_equivalences; auto. Qed.

  Fact bft_f_fix_oka_2 a x b l : bft_f (node a x b::l) = x::bft_f (l++a::b::nil).
  Proof. do 3 apply bft_f_equivalences; auto. Qed.

  Definition bft_forest t := bft_f (t::nil).

  Section bft_eq_bft_std.

    (** [bft] is extensionally equal to [bft_std] *)

    (** We characterize [niveaux] inductively *)

    Inductive g_niv : list (bt X) -> list (list X) -> Prop :=
      | in_gn_0 : g_niv nil nil
      | in_gn_1 : forall l rl, l <> nil -> g_niv (subtrees l) rl -> g_niv l (roots l :: rl).
    
    Lemma g_niv_app l rl m rm : g_niv l rl -> g_niv m rm -> g_niv (l++m) (zip (@app _) rl rm).
    Proof.
      intros H1; revert H1 m rm.
      induction 1 as [ | l rl H1 H2 IH2 ]; simpl; auto.
      induction 1 as [ | m rm H3 H4 IH4 ]; simpl; auto.
      * rewrite <- app_nil_end; constructor; auto.
      * rewrite <- map_app; constructor.
        + destruct l; try discriminate.
          destruct H1; auto.
        + rewrite subtrees_app; apply IH2; auto.
    Qed. 

    Lemma g_niv_niveaux t : g_niv (t::nil) (niveaux t).
    Proof.
      induction t as [ x | a Ha x b Hb ].
      * constructor 2; try discriminate.
        constructor.
      * simpl; constructor 2; try discriminate.
        apply (g_niv_app Ha Hb).
    Qed.

    Lemma g_niv_bft_f l rl : g_niv l rl -> g_bft_f l (concat rl).
    Proof. induction 1; simpl; constructor; auto. Qed.

    Lemma g_bft_f_bft_std t : g_bft_f (t::nil) (bft_std t).
    Proof. apply g_niv_bft_f, g_niv_niveaux. Qed.
 
    Theorem bft_forest_eq_bft_std t : bft_forest t = bft_std t.
    Proof. 
      apply g_bft_f_fun with (1 := bft_f_spec _).
      apply g_niv_bft_f, g_niv_niveaux.
    Qed.
 
  End bft_eq_bft_std.

End breadth_first_traversal.

Definition is_bfn_from n l := is_seq_from n (bft_f l).

Fact is_bfn_from_eq n l : is_bfn_from n l <-> bft_f l = seq_an n (lsum l).
Proof.
  unfold is_bfn_from.
  rewrite is_seq_from_spec, bft_f_length; tauto.
Qed.
