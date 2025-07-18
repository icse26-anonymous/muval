;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_list_fun$ 0 )
(declare-sort A_list_nat_fun$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort A_list_a_list_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun na$ ()Nat$ )
(declare-fun nth$ (A_list$ Nat$ )A$ )
(declare-fun bind$ (A_list$ A_a_list_fun$ )A_list$ )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun maps$ (A_a_list_fun$ )A_list_a_list_fun$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun member$ (A_list$ )A_bool_fun$ )
(declare-fun splice$ (A_list$ )A_list_a_list_fun$ )
(declare-fun fun_app$ (A_list_bool_fun$ A_list$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun list_of$ (A_llist$ )A_list$ )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_list_nat_fun$ A_list$ )Nat$ )
(declare-fun fun_app$c (A_list_a_list_fun$ A_list$ )A_list$ )
(declare-fun list_ex1$ (A_bool_fun$ )A_list_bool_fun$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun gen_length$ (Nat$ )A_list_nat_fun$ )
(assert (! (not (= (lnth$ (llist_of$ nil$ )na$ )(nth$ nil$ na$ ))):named a0 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 A_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a2 ))
(assert (! (forall ((?v0 A_list$ ))(= (lnull$ (llist_of$ ?v0 ))(= ?v0 nil$ ))):named a3 ))
(assert (! (forall ((?v0 A_list$ ))(= (list_of$ (llist_of$ ?v0 ))?v0 )):named a4 ))
(assert (! (forall ((?v0 A_list$ ))(= (= (llist_of$ ?v0 )lNil$ )(= ?v0 nil$ ))):named a5 ))
(assert (! (= (llist_of$ nil$ )lNil$ ):named a6 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (bind$ nil$ ?v0 )nil$ ):pattern ((bind$ nil$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$ (list_ex1$ ?v0 )nil$ )false ):pattern ((list_ex1$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a (member$ nil$ )?v0 )false ):pattern ((fun_app$a (member$ nil$ )?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_list$ ))(lfinite$ (llist_of$ ?v0 ))):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$b (gen_length$ ?v0 )nil$ )?v0 ):pattern ((gen_length$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$c (splice$ ?v0 )nil$ )?v0 ):pattern ((splice$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (fun_app$c (maps$ ?v0 )nil$ )nil$ ):pattern ((maps$ ?v0 )))):named a13 ))
(assert (! (= (lfinite$ lNil$ )true ):named a14 ))
(assert (! (= (list_of$ lNil$ )nil$ ):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$ ?v0 )(= (llist_of$ (list_of$ ?v0 ))?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (lnull$ ?v0 )(= ?v0 lNil$ )):pattern ((lnull$ ?v0 )))):named a17 ))
(check-sat )
;(get-unsat-core )
