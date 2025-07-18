;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort Enat_enat_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun xs$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun plus$ (Enat$ )Enat_enat_fun$ )
(declare-fun size$ (A_list$ )Nat$ )
(declare-fun fun_app$ (Enat_enat_fun$ Enat$ )Enat$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun list_of$ (A_llist$ )A_list$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun infinity$ ()Enat$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun the_enat$ (Enat$ )Nat$ )
(assert (! (not (exists ((?v0 Nat$ ))(= (llength$ xs$ )(enat$ ?v0 )))):named a0 ))
(assert (! (lfinite$ xs$ ):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (= (llength$ ?v0 )(enat$ ?v1 ))(lfinite$ ?v0 ))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (llength$ (lmap$ ?v0 ?v1 ))(llength$ ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_list$ ))(= (llength$ (llist_of$ ?v0 ))(enat$ (size$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (the_enat$ (enat$ ?v0 ))?v0 ):pattern ((enat$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$ ?v0 )(= (enat$ (size$ (list_of$ ?v0 )))(llength$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Enat$ )(?v2 Enat$ ))(= (= (fun_app$ (plus$ (enat$ ?v0 ))?v1 )(fun_app$ (plus$ (enat$ ?v0 ))?v2 ))(= ?v1 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ )(?v2 Enat$ ))(= (= (fun_app$ (plus$ ?v0 )(enat$ ?v1 ))(fun_app$ (plus$ ?v2 )(enat$ ?v1 )))(= ?v0 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 Enat$ ))(= (not (= ?v0 infinity$ ))(exists ((?v1 Nat$ ))(= ?v0 (enat$ ?v1 ))))):named a10 ))
(assert (! (forall ((?v0 Enat$ ))(= (forall ((?v1 Nat$ ))(not (= ?v0 (enat$ ?v1 ))))(= ?v0 infinity$ ))):named a11 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (plus$ ?v0 )infinity$ )infinity$ ):pattern ((plus$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 Enat$ ))(! (= (fun_app$ (plus$ infinity$ )?v0 )infinity$ ):pattern ((fun_app$ (plus$ infinity$ )?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lfinite$ (lmap$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a15 ))
(check-sat )
;(get-unsat-core )
