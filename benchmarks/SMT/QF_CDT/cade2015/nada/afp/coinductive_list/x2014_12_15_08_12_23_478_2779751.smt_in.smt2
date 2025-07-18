;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun uu$ ()A_llist_bool_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun uua$ ()A_llist_a_llist_fun$ )
(declare-fun uub$ ()A_llist_bool_fun$ )
(declare-fun uuc$ (A_llist_a_llist_fun$ )A_llist_a_llist_fun$ )
(declare-fun uud$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun uue$ (Bool )A_llist_bool_fun_a_llist_bool_fun_fun$ )
(declare-fun uuf$ (A_llist_bool_fun$ )A_llist_bool_fun_a_llist_bool_fun_fun$ )
(declare-fun uug$ (A_llist_bool_fun$ )A_llist_bool_fun_a_llist_bool_fun_fun$ )
(declare-fun uuh$ (A_llist_bool_fun$ )A_llist_bool_fun_a_llist_bool_fun_fun$ )
(declare-fun uui$ (A_llist_bool_fun$ )A_llist_bool_fun_a_llist_bool_fun_fun$ )
(declare-fun uuj$ (Bool )A_llist_bool_fun$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun mcont$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$ )Bool )
(declare-fun compact$ (A_llist_set_a_llist_fun$ )A_llist_a_llist_bool_fun_fun_a_llist_bool_fun_fun$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$c (A_llist_bool_fun_a_llist_bool_fun_fun$ A_llist_bool_fun$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (A_llist_a_llist_bool_fun_fun_a_llist_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ )A_llist_bool_fun$ )
(declare-fun admissible$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_bool_fun$ )Bool )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uu$ ?v0 )(not (fun_app$ (fun_app$a lprefix$ xs$ )(ltl$ ?v0 )))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uub$ ?v0 )(not (fun_app$ (fun_app$a lprefix$ xs$ )?v0 ))):pattern ((fun_app$ uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$b uua$ ?v0 )(ltl$ ?v0 )):pattern ((fun_app$b uua$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist$ ))(! (= (fun_app$b (uuc$ ?v0 )?v1 )(ltl$ (fun_app$b ?v0 ?v1 ))):pattern ((fun_app$b (uuc$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_bool_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$c (uuf$ ?v0 )?v1 )?v2 )(=> (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$c (uuf$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_bool_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$c (uug$ ?v0 )?v1 )?v2 )(=> (fun_app$ ?v1 ?v2 )(fun_app$ ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$c (uug$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_bool_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$c (uui$ ?v0 )?v1 )?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$c (uui$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_bool_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$c (uuh$ ?v0 )?v1 )?v2 )(= (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$c (uuh$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 Bool )(?v1 A_llist_bool_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$c (uue$ ?v0 )?v1 )?v2 )(=> ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$c (uue$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$b (uud$ ?v0 )?v1 )?v0 ):pattern ((fun_app$b (uud$ ?v0 )?v1 )))):named a9 ))
(assert (! (forall ((?v0 Bool )(?v1 A_llist$ ))(! (= (fun_app$ (uuj$ ?v0 )?v1 )?v0 ):pattern ((fun_app$ (uuj$ ?v0 )?v1 )))):named a10 ))
(assert (! (not (admissible$ lSup$ lprefix$ uu$ )):named a11 ))
(assert (! (mcont$ lSup$ lprefix$ lSup$ lprefix$ uua$ ):named a12 ))
(assert (! (admissible$ lSup$ lprefix$ uub$ ):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a14 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v0 )):named a15 ))
(assert (! (fun_app$ (fun_app$d (compact$ lSup$ )lprefix$ )xs$ ):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v1 ))(or (fun_app$ (fun_app$a lprefix$ ?v0 )?v2 )(fun_app$ (fun_app$a lprefix$ ?v2 )?v0 )))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a20 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ ?v1 )?v2 ))(fun_app$ (fun_app$a lprefix$ ?v0 )?v2 ))):named a21 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (fun_app$ (fun_app$a lprefix$ ?v0 )?v1 )(fun_app$ (fun_app$a lprefix$ (ltl$ ?v0 ))(ltl$ ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ ))(=> (mcont$ ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$ ?v0 ?v1 lSup$ lprefix$ (uuc$ ?v2 )))):named a23 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist$ ))(mcont$ ?v0 ?v1 lSup$ lprefix$ (uud$ ?v2 ))):named a24 ))
(assert (! (forall ((?v0 Bool )(?v1 A_llist_set_a_llist_fun$ )(?v2 A_llist_a_llist_bool_fun_fun$ )(?v3 A_llist_bool_fun$ ))(=> (=> ?v0 (admissible$ ?v1 ?v2 ?v3 ))(admissible$ ?v1 ?v2 (fun_app$c (uue$ ?v0 )?v3 )))):named a25 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_bool_fun$ )(?v3 A_llist_bool_fun$ ))(=> (and (admissible$ ?v0 ?v1 (fun_app$c (uuf$ ?v2 )?v3 ))(admissible$ ?v0 ?v1 (fun_app$c (uug$ ?v2 )?v3 )))(admissible$ ?v0 ?v1 (fun_app$c (uuh$ ?v2 )?v3 )))):named a26 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_bool_fun$ )(?v3 A_llist_bool_fun$ ))(=> (and (admissible$ ?v0 ?v1 ?v2 )(admissible$ ?v0 ?v1 ?v3 ))(admissible$ ?v0 ?v1 (fun_app$c (uui$ ?v2 )?v3 )))):named a27 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 Bool ))(admissible$ ?v0 ?v1 (uuj$ ?v2 ))):named a28 ))
(check-sat )
;(get-unsat-core )
