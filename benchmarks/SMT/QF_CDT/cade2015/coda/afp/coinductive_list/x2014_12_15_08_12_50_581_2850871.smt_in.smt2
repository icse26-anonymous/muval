;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun bot$ ()A_llist_set$ )
(declare-fun uua$ ()A_llist_bool_fun$ )
(declare-fun uub$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$ )Bool )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun collect$ (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun compact$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist$ )Bool )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun admissible$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_bool_fun$ )Bool )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )(not (= ?v0 xs$ )))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(not (fun_app$ (fun_app$a lprefix$ xs$ )?v0 ))):pattern ((fun_app$ uua$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (uub$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 )):pattern ((fun_app$ (uub$ ?v0 )?v1 )))):named a2 ))
(assert (! (not (not (fun_app$ (fun_app$a lprefix$ xs$ )(fun_app$b lSup$ (collect$ uu$ ))))):named a3 ))
(assert (! (not (= (collect$ uu$ )bot$ )):named a4 ))
(assert (! (chain$ lprefix$ (collect$ uu$ )):named a5 ))
(assert (! (admissible$ lSup$ lprefix$ uua$ ):named a6 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a8 ))
(assert (! (not (lfinite$ xs$ )):named a9 ))
(assert (! (compact$ lSup$ lprefix$ xs$ ):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a15 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (fun_app$b lSup$ ?v0 ))?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))))(fun_app$ (fun_app$a lprefix$ (fun_app$b lSup$ ?v0 ))?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(fun_app$b lSup$ ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (chain$ lprefix$ ?v0 )(member$ ?v1 ?v0 ))(fun_app$ (fun_app$a lprefix$ ?v1 )(fun_app$b lSup$ ?v0 )))):named a19 ))
(assert (! (forall ((?v0 A_llist$ ))(chain$ lprefix$ (collect$ (uub$ ?v0 )))):named a20 ))
(check-sat )
;(get-unsat-core )
