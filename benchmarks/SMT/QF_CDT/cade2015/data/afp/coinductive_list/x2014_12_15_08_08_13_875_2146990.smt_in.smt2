;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_set_a_set_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()A_llist$ )
(declare-fun sup$ (A_set$ )A_set_a_set_fun$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_set_a_set_fun$ A_set$ )A_set$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (A_set$ A_set$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lmember$ (A$ A_llist$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun gen_lset$ (A_set$ A_llist$ )A_set$ )
(assert (! (not (= (lset$ (lappend$ xs$ ys$ ))(ite (lfinite$ xs$ )(fun_app$ (sup$ (lset$ xs$ ))(lset$ ys$ ))(lset$ xs$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (lfinite$ (lappend$ ?v0 ?v1 ))(and (lfinite$ ?v0 )(lfinite$ ?v1 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (lfinite$ ?v0 )(= (lset$ (lappend$ ?v0 ?v1 ))(fun_app$ (sup$ (lset$ ?v0 ))(lset$ ?v1 ))))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (lappend$ (lappend$ ?v0 ?v1 )?v2 )(lappend$ ?v0 (lappend$ ?v1 ?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (=> (not (lfinite$ ?v0 ))(= (lappend$ ?v0 ?v1 )?v0 )):pattern ((lappend$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(= (member$ ?v0 (fun_app$ (sup$ ?v1 )?v2 ))(or (member$ ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(=> (=> (not (member$ ?v0 ?v1 ))(member$ ?v0 ?v2 ))(member$ ?v0 (fun_app$ (sup$ ?v2 )?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (sup$ (fun_app$ (sup$ ?v0 )?v1 ))?v1 )(fun_app$ (sup$ ?v0 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (sup$ ?v0 )(fun_app$ (sup$ ?v0 )?v1 ))(fun_app$ (sup$ ?v0 )?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (sup$ ?v0 )(fun_app$ (sup$ ?v0 )?v1 ))(fun_app$ (sup$ ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (sup$ ?v0 )?v0 )?v0 ):pattern ((sup$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (sup$ ?v0 )?v0 )?v0 ):pattern ((sup$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_llist$ ))(! (= (gen_lset$ ?v0 ?v1 )(fun_app$ (sup$ ?v0 )(lset$ ?v1 ))):pattern ((gen_lset$ ?v0 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(= (member$ ?v0 (lset$ ?v1 ))(lmember$ ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(less_eq$ (lset$ (lappend$ ?v0 ?v1 ))(fun_app$ (sup$ (lset$ ?v0 ))(lset$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_bool_fun$ ))(= (exists ((?v3 A$ ))(and (member$ ?v3 (fun_app$ (sup$ ?v0 )?v1 ))(fun_app$a ?v2 ?v3 )))(or (exists ((?v3 A$ ))(and (member$ ?v3 ?v0 )(fun_app$a ?v2 ?v3 )))(exists ((?v3 A$ ))(and (member$ ?v3 ?v1 )(fun_app$a ?v2 ?v3 )))))):named a15 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (forall ((?v2 A$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$ ?v0 ?v1 ))):named a16 ))
(check-sat )
;(get-unsat-core )
