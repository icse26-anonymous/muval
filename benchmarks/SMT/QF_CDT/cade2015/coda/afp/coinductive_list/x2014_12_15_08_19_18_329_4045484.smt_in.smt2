;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-fun us$ ()A_llist$ )
(declare-fun vs$ ()A_llist$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun plus$ (Enat$ Enat$ )Enat$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(assert (! (not (= xs$ us$ )):named a0 ))
(assert (! (= (llength$ xs$ )(llength$ us$ )):named a1 ))
(assert (! (= (fun_app$ (lappend$ xs$ )ys$ )(fun_app$ (lappend$ us$ )vs$ )):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0 )?v1 ))?v2 )(fun_app$ (lappend$ ?v0 )(fun_app$ (lappend$ ?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (llength$ (fun_app$ (lappend$ ?v0 )?v1 ))(plus$ (llength$ ?v0 )(llength$ ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (llength$ (lmap$ ?v0 ?v1 ))(llength$ ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$ (fun_app$ (lappend$ ?v0 )?v1 )))(or (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (lnull$ ?v0 )(lnull$ ?v1 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )(lCons$ ?v0 (fun_app$ (lappend$ ?v1 )?v2 ))):pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (fun_app$ (lappend$ ?v0 )?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a13 ))
(assert (! (= (fun_app$ (lappend$ lNil$ )lNil$ )lNil$ ):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (lprefix$ ?v0 ?v1 )(lprefix$ (fun_app$ (lappend$ ?v2 )?v0 )(fun_app$ (lappend$ ?v2 )?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a16 ))
(assert (! (forall ((?v0 A_llist$ ))(lprefix$ ?v0 ?v0 )):named a17 ))
(check-sat )
;(get-unsat-core )
