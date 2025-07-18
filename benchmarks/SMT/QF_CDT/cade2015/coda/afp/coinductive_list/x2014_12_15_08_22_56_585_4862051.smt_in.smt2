;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_set_a_set_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun p$ ()A_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun inf$ (A_set$ )A_set_a_set_fun$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun collect$ (A_bool_fun$ )A_set$ )
(declare-fun fun_app$ (A_set_a_set_fun$ A_set$ )A_set$ )
(declare-fun less_eq$ (A_set$ A_set$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun ltakeWhile$ (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (not (less_eq$ (lset$ (ltakeWhile$ p$ xs$ ))(fun_app$ (inf$ (lset$ xs$ ))(collect$ p$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_bool_fun$ ))(! (=> (forall ((?v2 A$ ))(=> (member$ ?v2 (lset$ ?v0 ))(fun_app$a ?v1 ?v2 )))(= (ltakeWhile$ ?v1 ?v0 )?v0 )):pattern ((ltakeWhile$ ?v1 ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A$ )(?v1 A_bool_fun$ )(?v2 A_llist$ ))(=> (member$ ?v0 (lset$ (ltakeWhile$ ?v1 ?v2 )))(and (member$ ?v0 (lset$ ?v2 ))(fun_app$a ?v1 ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set$ ))(= (less_eq$ ?v0 (fun_app$ (inf$ ?v1 )?v2 ))(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v0 ?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set$ ))(= (less_eq$ ?v0 (fun_app$ (inf$ ?v1 )?v2 ))(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v0 ?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set$ ))(= (less_eq$ ?v0 (fun_app$ (inf$ ?v1 )?v2 ))(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v0 ?v2 )))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(= (member$ ?v0 (fun_app$ (inf$ ?v1 )?v2 ))(and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(=> (and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 ))(member$ ?v0 (fun_app$ (inf$ ?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ (fun_app$ (inf$ ?v0 )?v1 ))?v1 )(fun_app$ (inf$ ?v0 )?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ (fun_app$ (inf$ ?v0 )?v1 ))?v1 )(fun_app$ (inf$ ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )(fun_app$ (inf$ ?v0 )?v1 ))(fun_app$ (inf$ ?v0 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )(fun_app$ (inf$ ?v0 )?v1 ))(fun_app$ (inf$ ?v0 )?v1 ))):named a11 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (inf$ ?v0 )?v0 )?v0 ):pattern ((inf$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (inf$ ?v0 )?v0 )?v0 ):pattern ((inf$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (forall ((?v2 A$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$ ?v0 ?v1 ))):named a15 ))
(check-sat )
;(get-unsat-core )
