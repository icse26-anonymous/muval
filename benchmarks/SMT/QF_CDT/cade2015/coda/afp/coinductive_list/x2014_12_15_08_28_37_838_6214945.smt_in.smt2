;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun r$ ()A_a_bool_fun_fun$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()A$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun y$a ()A$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun ys$a ()A_llist$ )
(declare-fun ysa$ ()A_llist$ )
(declare-fun xs_a$ ()A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llexord$ (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(assert (! (not (and (not (lnull$ ysa$ ))(=> (not (lnull$ ysa$ ))(or (fun_app$ (fun_app$a r$ (lhd$ xsa$ ))(lhd$ ysa$ ))(and (= (lhd$ xsa$ )(lhd$ ysa$ ))(or (or (= (ltl$ xsa$ )(ltl$ ysa$ ))(exists ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(and (lfinite$ ?v0 )(and (= (ltl$ xsa$ )(lappend$ ?v0 ?v1 ))(and (= (ltl$ ysa$ )(lappend$ ?v0 (lCons$ ?v2 ?v3 )))(or (= ?v1 lNil$ )(fun_app$ (fun_app$a r$ (lhd$ ?v1 ))?v2 )))))))(llexord$ r$ (ltl$ xsa$ )(ltl$ ysa$ )))))))):named a0 ))
(assert (! (lfinite$ zs$ ):named a1 ))
(assert (! (= xsa$ (lCons$ x$ xs$ )):named a2 ))
(assert (! (= ysa$ (lCons$ y$ ys$ )):named a3 ))
(assert (! (= xsa$ (lappend$ zs$ xs_a$ )):named a4 ))
(assert (! (= ysa$ (lappend$ zs$ (lCons$ y$a ys$a ))):named a5 ))
(assert (! (or (= xs_a$ lNil$ )(fun_app$ (fun_app$a r$ (lhd$ xs_a$ ))y$a )):named a6 ))
(assert (! (not (lnull$ xsa$ )):named a7 ))
(assert (! (=> (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (= ysa$ (lCons$ ?v0 ?v1 ))false ))false ):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a9 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(llexord$ ?v0 ?v1 ?v1 )):named a10 ))
(assert (! (or (= xsa$ ysa$ )(exists ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(and (lfinite$ ?v0 )(and (= xsa$ (lappend$ ?v0 ?v1 ))(and (= ysa$ (lappend$ ?v0 (lCons$ ?v2 ?v3 )))(or (= ?v1 lNil$ )(fun_app$ (fun_app$a r$ (lhd$ ?v1 ))?v2 ))))))):named a11 ))
(assert (! (exists ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(and (lfinite$ ?v0 )(and (= xsa$ (lappend$ ?v0 ?v1 ))(and (= ysa$ (lappend$ ?v0 (lCons$ ?v2 ?v3 )))(or (= ?v1 lNil$ )(fun_app$ (fun_app$a r$ (lhd$ ?v1 ))?v2 )))))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (lappend$ (lCons$ ?v0 ?v1 )?v2 )(lCons$ ?v0 (lappend$ ?v1 ?v2 ))):pattern ((lappend$ (lCons$ ?v0 ?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (not (lnull$ (lappend$ ?v0 ?v1 )))(or (not (lnull$ ?v0 ))(not (lnull$ ?v1 ))))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lnull$ (lappend$ ?v0 ?v1 ))(and (lnull$ ?v0 )(lnull$ ?v1 )))):named a17 ))
(check-sat )
;(get-unsat-core )
