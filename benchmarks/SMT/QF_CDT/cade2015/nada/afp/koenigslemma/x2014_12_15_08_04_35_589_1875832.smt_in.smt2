;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_list_a_list_fun$ 0 )
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun n$ ()A$ )
(declare-fun n$a ()A$ )
(declare-fun graph$ ()A_a_bool_fun_fun$ )
(declare-fun paths$ (A_a_bool_fun_fun$ )A_llist_set$ )
(declare-fun append$ (A_list$ )A_list_a_list_fun$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (A_list_a_list_fun$ A_list$ )A_list$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun connected$ (A_a_bool_fun_fun$ )Bool )
(assert (! (not (exists ((?v0 A_list$ ))(member$ (llist_of$ (cons$ n$ (fun_app$ (append$ ?v0 )(cons$ n$a nil$ ))))(paths$ graph$ )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(exists ((?v2 A_list$ ))(member$ (llist_of$ (cons$ ?v0 (fun_app$ (append$ ?v2 )(cons$ ?v1 nil$ ))))(paths$ graph$ )))):named a1 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(= (connected$ ?v0 )(forall ((?v1 A$ )(?v2 A$ ))(exists ((?v3 A_list$ ))(member$ (llist_of$ (cons$ ?v1 (fun_app$ (append$ ?v3 )(cons$ ?v2 nil$ ))))(paths$ ?v0 )))))):named a2 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A$ )(?v2 A_list$ )(?v3 A$ ))(= (= (fun_app$ (append$ ?v0 )(cons$ ?v1 nil$ ))(fun_app$ (append$ ?v2 )(cons$ ?v3 nil$ )))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v1 )(= ?v0 nil$ ))):named a4 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v0 )(= ?v1 nil$ ))):named a5 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= ?v0 (fun_app$ (append$ ?v1 )?v0 ))(= ?v1 nil$ ))):named a6 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= ?v0 (fun_app$ (append$ ?v0 )?v1 ))(= ?v1 nil$ ))):named a7 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= nil$ (fun_app$ (append$ ?v0 )?v1 ))(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a8 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )nil$ )(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a9 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$ (append$ ?v0 )nil$ )?v0 ):pattern ((append$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A$ )(?v3 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(cons$ ?v2 ?v3 ))(or (and (= ?v0 nil$ )(= ?v1 (cons$ ?v2 ?v3 )))(exists ((?v4 A_list$ ))(and (= ?v0 (cons$ ?v2 ?v4 ))(= (fun_app$ (append$ ?v4 )?v1 )?v3 )))))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ )(?v2 A_list$ )(?v3 A_list$ ))(= (= (cons$ ?v0 ?v1 )(fun_app$ (append$ ?v2 )?v3 ))(or (and (= ?v2 nil$ )(= (cons$ ?v0 ?v1 )?v3 ))(exists ((?v4 A_list$ ))(and (= (cons$ ?v0 ?v4 )?v2 )(= ?v1 (fun_app$ (append$ ?v4 )?v3 ))))))):named a12 ))
(assert (! (forall ((?v0 A_list$ ))(=> (and (=> (= ?v0 nil$ )false )(forall ((?v1 A_list$ )(?v2 A$ ))(=> (= ?v0 (fun_app$ (append$ ?v1 )(cons$ ?v2 nil$ )))false )))false )):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ )(?v2 A$ )(?v3 A_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (fun_app$ (append$ (fun_app$ (append$ ?v0 )?v1 ))?v2 )(fun_app$ (append$ ?v0 )(fun_app$ (append$ ?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v2 )?v1 ))(= ?v0 ?v2 ))):named a16 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v0 )?v2 ))(= ?v1 ?v2 ))):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(not (= (cons$ ?v0 ?v1 )?v1 ))):named a18 ))
(check-sat )
;(get-unsat-core )
