;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun p$ ()A_llist_bool_fun$ )
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun zs$ ()A_llist$ )
(declare-fun uua$ ()A_llist_bool_fun$ )
(declare-fun uub$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun uuc$ (A_llist$ A_llist$ )A_llist_bool_fun$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$ )Bool )
(declare-fun collect$ (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun admissible$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_bool_fun$ )Bool )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )(and (fun_app$ (fun_app$a lprefix$ zs$ )?v0 )(lfinite$ ?v0 )))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )):pattern ((fun_app$ uua$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (uub$ ?v0 )?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v1 )?v0 )(lfinite$ ?v1 ))):pattern ((fun_app$ (uub$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (uuc$ ?v0 ?v1 )?v2 )(and (fun_app$ (fun_app$a lprefix$ ?v2 )?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(lfinite$ ?v2 )))):pattern ((fun_app$ (uuc$ ?v0 ?v1 )?v2 )))):named a3 ))
(assert (! (not (fun_app$ p$ (fun_app$b lSup$ (collect$ uu$ )))):named a4 ))
(assert (! (lfinite$ zs$ ):named a5 ))
(assert (! (admissible$ lSup$ lprefix$ p$ ):named a6 ))
(assert (! (fun_app$ (fun_app$a lprefix$ zs$ )xs$ ):named a7 ))
(assert (! (chain$ lprefix$ (collect$ uu$ )):named a8 ))
(assert (! (exists ((?v0 A_llist$ ))(and (fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )(and (lfinite$ ?v0 )(forall ((?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v1 )xs$ )(lfinite$ ?v1 )))(fun_app$ p$ ?v1 )))))):named a9 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a10 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a11 ))
(assert (! (chain$ lprefix$ (collect$ uua$ )):named a12 ))
(assert (! (=> (forall ((?v0 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )(and (lfinite$ ?v0 )(forall ((?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(and (fun_app$ (fun_app$a lprefix$ ?v1 )xs$ )(lfinite$ ?v1 )))(fun_app$ p$ ?v1 )))))false ))false ):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ zs$ )?v0 )(and (fun_app$ (fun_app$a lprefix$ ?v0 )xs$ )(lfinite$ ?v0 )))(fun_app$ p$ ?v0 ))):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$b lSup$ (collect$ (uub$ ?v0 )))?v0 )):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a20 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(lfinite$ ?v0 ))(= (fun_app$b lSup$ (collect$ (uuc$ ?v0 ?v1 )))?v1 ))):named a21 ))
(check-sat )
;(get-unsat-core )
