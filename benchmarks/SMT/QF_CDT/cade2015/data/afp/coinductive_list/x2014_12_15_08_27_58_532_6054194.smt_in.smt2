;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun r$ ()A_a_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun sup$ (A_set$ A_set$ )A_set$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun finite$ (A_set$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (A_set$ A_set$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llexord$ (A_a_bool_fun_fun$ A_llist$ A_llist$ )Bool )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun lprefix$ (A_llist$ A_llist$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun ldropWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (not (= (llexord$ r$ (lappend$ xs$ ys$ )(lappend$ xs$ zs$ ))(llexord$ r$ ys$ zs$ ))):named a0 ))
(assert (! (lfinite$ xs$ ):named a1 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (lset$ xs$ ))(not (fun_app$ (fun_app$a r$ ?v0 )?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(llexord$ ?v0 ?v1 ?v1 )):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lappend$ ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (member$ ?v0 (lset$ (lappend$ ?v1 ?v2 )))(or (member$ ?v0 (lset$ ?v1 ))(and (lfinite$ ?v1 )(member$ ?v0 (lset$ ?v2 )))))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (llexord$ ?v0 (lappend$ ?v1 ?v2 )(lappend$ ?v1 ?v3 ))(and (lfinite$ ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 (lset$ ?v1 ))(not (fun_app$ (fun_app$a ?v0 ?v4 )?v4 ))))))(llexord$ ?v0 ?v2 ?v3 ))):named a7 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (llexord$ ?v0 ?v1 ?v2 )(llexord$ ?v0 (lappend$ ?v3 ?v1 )(lappend$ ?v3 ?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (lappend$ ?v0 ?v1 )?v0 )):pattern ((lappend$ ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(llexord$ ?v0 ?v1 (lappend$ ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (lfinite$ ?v0 )(= (lset$ (lappend$ ?v0 ?v1 ))(sup$ (lset$ ?v0 )(lset$ ?v1 ))))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(lmember$ ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lset$ (lappend$ ?v0 ?v1 ))(ite (lfinite$ ?v0 )(sup$ (lset$ ?v0 )(lset$ ?v1 ))(lset$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(exists ((?v2 A_llist$ )(?v3 A_llist$ ))(and (= ?v1 (lappend$ ?v2 (lCons$ ?v0 ?v3 )))(and (lfinite$ ?v2 )(not (member$ ?v0 (lset$ ?v2 )))))))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(=> (member$ ?v0 (lset$ ?v1 ))(exists ((?v2 A_llist$ )(?v3 A_llist$ ))(and (= ?v1 (lappend$ ?v2 (lCons$ ?v0 ?v3 )))(lfinite$ ?v2 ))))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lprefix$ (lappend$ ?v0 ?v1 )(lappend$ ?v0 ?v2 ))(=> (lfinite$ ?v0 )(lprefix$ ?v1 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ ))(= (lfinite$ (ldropWhile$ ?v0 ?v1 ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (lset$ ?v1 ))(not (fun_app$ ?v0 ?v2 ))))(lfinite$ ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(less_eq$ (lset$ ?v0 )(lset$ (lappend$ ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (lfinite$ ?v0 )(finite$ (lset$ ?v0 )))):named a19 ))
(check-sat )
;(get-unsat-core )
