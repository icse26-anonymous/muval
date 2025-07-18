;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort B_a_llist_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort B_a_llist_fun_bool_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_a_llist_fun_set_b_a_llist_fun_fun$ 0 )
(declare-sort B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_lub$ (A_llist_set_a_llist_fun$ )B_a_llist_fun_set_b_a_llist_fun_fun$ )
(declare-fun fun_ord$ (A_llist_a_llist_bool_fun_fun$ )B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (B_a_llist_fun_bool_fun$ B_a_llist_fun$ )Bool )
(declare-fun fun_app$c (B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ B_a_llist_fun$ )B_a_llist_fun_bool_fun$ )
(declare-fun fun_app$d (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun lub_singleton$ (A_llist_set_a_llist_fun$ )Bool )
(declare-fun partial_function_definitions$ (B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ B_a_llist_fun_set_b_a_llist_fun_fun$ )Bool )
(declare-fun partial_function_definitions$a (A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ )Bool )
(assert (! (not (partial_function_definitions$ (fun_ord$ lprefix$ )(fun_lub$ lSup$ ))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a7 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set_a_llist_fun$ ))(=> (partial_function_definitions$a ?v0 ?v1 )(partial_function_definitions$ (fun_ord$ ?v0 )(fun_lub$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set_a_llist_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (partial_function_definitions$a ?v0 ?v1 )(and (fun_app$ (fun_app$a ?v0 ?v2 )?v3 )(fun_app$ (fun_app$a ?v0 ?v3 )?v2 )))(= ?v2 ?v3 ))):named a9 ))
(assert (! (forall ((?v0 B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ )(?v1 B_a_llist_fun_set_b_a_llist_fun_fun$ )(?v2 B_a_llist_fun$ )(?v3 B_a_llist_fun$ ))(=> (and (partial_function_definitions$ ?v0 ?v1 )(and (fun_app$b (fun_app$c ?v0 ?v2 )?v3 )(fun_app$b (fun_app$c ?v0 ?v3 )?v2 )))(= ?v2 ?v3 ))):named a10 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set_a_llist_fun$ )(?v2 A_llist$ )(?v3 A_llist$ )(?v4 A_llist$ ))(=> (and (partial_function_definitions$a ?v0 ?v1 )(and (fun_app$ (fun_app$a ?v0 ?v2 )?v3 )(fun_app$ (fun_app$a ?v0 ?v3 )?v4 )))(fun_app$ (fun_app$a ?v0 ?v2 )?v4 ))):named a11 ))
(assert (! (forall ((?v0 B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ )(?v1 B_a_llist_fun_set_b_a_llist_fun_fun$ )(?v2 B_a_llist_fun$ )(?v3 B_a_llist_fun$ )(?v4 B_a_llist_fun$ ))(=> (and (partial_function_definitions$ ?v0 ?v1 )(and (fun_app$b (fun_app$c ?v0 ?v2 )?v3 )(fun_app$b (fun_app$c ?v0 ?v3 )?v4 )))(fun_app$b (fun_app$c ?v0 ?v2 )?v4 ))):named a12 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set_a_llist_fun$ )(?v2 A_llist$ ))(=> (partial_function_definitions$a ?v0 ?v1 )(fun_app$ (fun_app$a ?v0 ?v2 )?v2 ))):named a13 ))
(assert (! (forall ((?v0 B_a_llist_fun_b_a_llist_fun_bool_fun_fun$ )(?v1 B_a_llist_fun_set_b_a_llist_fun_fun$ )(?v2 B_a_llist_fun$ ))(=> (partial_function_definitions$ ?v0 ?v1 )(fun_app$b (fun_app$c ?v0 ?v2 )?v2 ))):named a14 ))
(assert (! (partial_function_definitions$a lprefix$ lSup$ ):named a15 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (fun_app$d lSup$ ?v0 ))?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (fun_app$d lSup$ ?v0 ))?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(fun_app$d lSup$ ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(fun_app$d lSup$ ?v0 )))):named a19 ))
(assert (! (lub_singleton$ lSup$ ):named a20 ))
(check-sat )
;(get-unsat-core )
