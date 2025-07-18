;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun na$ ()Nat$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun xsa$ ()A_list$ )
(declare-fun drop$ (Nat$ A_list$ )A_list$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun ldropn$ (Nat$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun list_of$ (A_llist$ )A_list$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(assert (! (not (= (fun_app$ (ldropn$ (suc$ na$ ))(llist_of$ xsa$ ))(llist_of$ (drop$ (suc$ na$ )xsa$ )))):named a0 ))
(assert (! (forall ((?v0 A_list$ ))(= (fun_app$ (ldropn$ na$ )(llist_of$ ?v0 ))(llist_of$ (drop$ na$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (suc$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (ldropn$ (suc$ ?v0 ))(lCons$ ?v1 ?v2 ))(fun_app$ (ldropn$ ?v0 )?v2 )):pattern ((fun_app$ (ldropn$ (suc$ ?v0 ))(lCons$ ?v1 ?v2 ))))):named a7 ))
(assert (! (forall ((?v0 A_list$ ))(= (list_of$ (llist_of$ ?v0 ))?v0 )):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(! (= (fun_app$ (ldropn$ (suc$ ?v0 ))?v1 )(fun_app$ (ldropn$ ?v0 )(ltl$ ?v1 ))):pattern ((fun_app$ (ldropn$ (suc$ ?v0 ))?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (ldropn$ zero$ )?v0 )?v0 ):pattern ((fun_app$ (ldropn$ zero$ )?v0 )))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 A_list$ ))(! (= (drop$ (suc$ ?v0 )(cons$ ?v1 ?v2 ))(drop$ ?v0 ?v2 )):pattern ((drop$ (suc$ ?v0 )(cons$ ?v1 ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_llist$ ))(= (fun_app$ (ldropn$ ?v0 )(fun_app$ (ldropn$ ?v1 )?v2 ))(fun_app$ (ldropn$ (plus$ ?v0 ?v1 ))?v2 ))):named a12 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (ldropn$ ?v0 )lNil$ )lNil$ ):pattern ((ldropn$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ )(?v2 A$ )(?v3 A_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (plus$ ?v0 ?v1 )zero$ )(and (= ?v0 zero$ )(= ?v1 zero$ )))):named a16 ))
(check-sat )
;(get-unsat-core )
