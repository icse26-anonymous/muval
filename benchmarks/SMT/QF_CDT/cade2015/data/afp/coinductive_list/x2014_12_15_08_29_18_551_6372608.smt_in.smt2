;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-fun r$ ()A_a_bool_fun_fun$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()A$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_list$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun xs$a ()A_llist$ )
(declare-fun xs$b ()A_list$ )
(declare-fun xs$c ()A_list$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llexord$ (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun llist_of$ (A_list$ )A_llist$ )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (not (fun_app$ (fun_app$a r$ (lhd$ xs$ ))y$ )):named a0 ))
(assert (! (= xs$ (lCons$ x$ xs$a )):named a1 ))
(assert (! (or (= xs$ lNil$ )(fun_app$ (fun_app$a r$ (lhd$ xs$ ))y$ )):named a2 ))
(assert (! (=> (forall ((?v0 A_list$ ))(=> (= xs$ (llist_of$ ?v0 ))false ))false ):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lhd$ (lCons$ ?v0 ?v1 ))?v0 ):pattern ((lCons$ ?v0 ?v1 )))):named a4 ))
(assert (! (lfinite$ xs$ ):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a6 ))
(assert (! (= xs$ (llist_of$ xs$b )):named a7 ))
(assert (! (llexord$ r$ (llist_of$ xs$c )(llist_of$ ys$ )):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lhd$ (iterates$ ?v0 ?v1 ))?v1 )):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(=> (and (=> (or (lnull$ ?v0 )(not (fun_app$ ?v1 (lhd$ ?v0 ))))false )(=> (and (not (lnull$ ?v0 ))(fun_app$ ?v1 (lhd$ ?v0 )))false ))false )):named a10 ))
(assert (! (= (llist_of$ xs$c )(lappend$ zs$ xs$ )):named a11 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (= (ltakeWhile$ ?v0 ?v1 )lNil$ )(=> (not (= ?v1 lNil$ ))(not (fun_app$ ?v0 (lhd$ ?v1 )))))):named a12 ))
(assert (! (lfinite$ zs$ ):named a13 ))
(assert (! (=> (forall ((?v0 A_list$ ))(=> (= zs$ (llist_of$ ?v0 ))false ))false ):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= (llist_of$ ?v0 )(llist_of$ ?v1 ))(= ?v0 ?v1 ))):named a15 ))
(check-sat )
;(get-unsat-core )
