;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_llist_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_a_llist_prod_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_fun$ 0 )
(declare-sort A_llist_a_a_llist_a_llist_fun_fun_fun$ 0 )
(declare-sort A_a_llist_a_llist_prod_a_llist_fun_fun$ 0 )
(declare-sort A_a_llist_a_a_llist_a_llist_fun_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ 0 )
(declare-sort A_a_llist_a_llist_fun_fun_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ 0 )
(declare-sort A_llist_a_a_llist_a_a_llist_a_llist_fun_fun_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_a_llist_prod_fun_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun_a_llist_a_llist_prod_set_a_llist_a_llist_prod_fun_fun$ 0 )
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((A_llist_a_llist_prod$ (pair$ (fst$ A_llist$ )(snd$ A_llist$ )))))
(declare-fun f$ ()A_llist_a_llist_a_llist_fun_fun$ )
(declare-fun uu$ (A_llist$ )A_llist_a_a_llist_a_a_llist_a_llist_fun_fun_fun_fun_fun$ )
(declare-fun uua$ (A_llist$ )A_llist_a_a_llist_a_llist_fun_fun_fun$ )
(declare-fun uub$ ()A_llist_a_llist_a_llist_fun_fun$ )
(declare-fun uuc$ (A$ )A_bool_fun$ )
(declare-fun uud$ (A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )
(declare-fun uue$ (A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )A_llist_a_llist_a_llist_prod_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uuf$ (A_llist_a_llist_a_llist_fun_fun$ )A_llist_a_llist_a_llist_fun_fun$ )
(declare-fun uug$ (A_llist_a_llist_a_llist_fun_fun$ )A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uuh$ (A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uui$ (A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uuj$ (A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uuk$ (A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uul$ (A_llist_a_llist_prod_a_llist_fun$ )A_llist_a_llist_a_llist_prod_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uum$ (A_llist_a_llist_fun$ )A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uun$ (A_llist_a_llist_fun$ )A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uuo$ (A_llist_a_llist_prod_a_llist_fun$ )A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uup$ (A_llist_a_llist_fun$ )A_a_llist_a_llist_fun_fun$ )
(declare-fun uuq$ (A_llist_a_llist_prod_a_llist_fun$ )A_a_llist_a_llist_prod_a_llist_fun_fun$ )
(declare-fun uur$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun uus$ (A_llist$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun less$ ()A_a_bool_fun_fun$ )
(declare-fun mcont$ (A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_prod_a_llist_fun$ )Bool )
(declare-fun mcont$a (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$ )Bool )
(declare-fun mcont$b (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ A_llist_a_llist_a_llist_prod_fun$ )Bool )
(declare-fun mcont$c (A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ )Bool )
(declare-fun collect$ (A_bool_fun$ )A_set$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_llist_a_llist_a_llist_fun_fun$ A_llist$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$b (A_a_llist_a_llist_fun_fun_a_llist_a_llist_fun_fun$ A_a_llist_a_llist_fun_fun$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$c (A_llist_a_a_llist_a_llist_fun_fun_fun$ A_llist$ )A_a_llist_a_llist_fun_fun$ )
(declare-fun fun_app$d (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$e (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$f (A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ A_llist_a_llist_fun$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$g (A_llist_a_llist_a_llist_prod_fun_a_llist_a_llist_fun_fun$ A_llist_a_llist_a_llist_prod_fun$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$h (A_llist_a_llist_prod_a_llist_fun$ A_llist_a_llist_prod$ )A_llist$ )
(declare-fun fun_app$i (A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun fun_app$j (A_llist_a_llist_a_llist_prod_fun$ A_llist$ )A_llist_a_llist_prod$ )
(declare-fun fun_app$k (A_llist_a_llist_prod_a_llist_fun_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist_a_llist_prod_a_llist_fun$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun fun_app$l (A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ A_llist_a_llist_prod$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$m (A_llist_a_llist_prod_a_llist_a_llist_prod_fun_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun fun_app$n (A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ A_llist_a_llist_prod$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun fun_app$o (A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod$ )A_llist_a_llist_prod$ )
(declare-fun fun_app$p (A_a_llist_a_llist_fun_fun$ A$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$q (A_a_llist_a_llist_prod_a_llist_fun_fun$ A$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun fun_app$r (A_a_llist_a_a_llist_a_llist_fun_fun_fun_fun$ A$ )A_llist_a_a_llist_a_llist_fun_fun_fun$ )
(declare-fun fun_app$s (A_llist_a_a_llist_a_a_llist_a_llist_fun_fun_fun_fun_fun$ A_llist$ )A_a_llist_a_a_llist_a_llist_fun_fun_fun_fun$ )
(declare-fun fun_app$t (A_llist_set_a_llist_fun_a_llist_a_llist_prod_set_a_llist_a_llist_prod_fun_fun$ A_llist_set_a_llist_fun$ )A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )
(declare-fun fun_app$u (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$v (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun lessThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun prod_lub$ (A_llist_set_a_llist_fun$ )A_llist_set_a_llist_fun_a_llist_a_llist_prod_set_a_llist_a_llist_prod_fun_fun$ )
(declare-fun rel_prod$ (A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$ )A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )
(declare-fun case_prod$ (A_llist_a_llist_a_llist_fun_fun$ )A_llist_a_llist_prod_a_llist_fun$ )
(declare-fun case_llist$ (A_llist$ )A_a_llist_a_llist_fun_fun_a_llist_a_llist_fun_fun$ )
(declare-fun greaterThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (fun_app$a uub$ ?v0 )?v1 )(fun_app$ (fun_app$b (case_llist$ lNil$ )(fun_app$c (uua$ ?v0 )?v1 ))?v0 )):pattern ((fun_app$ (fun_app$a uub$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$d (uuc$ ?v0 )?v1 )(fun_app$d (fun_app$e less$ ?v1 )?v0 )):pattern ((fun_app$d (uuc$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_fun_fun$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$f (uug$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$f (uug$ ?v0 )?v1 )?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v1 A_llist_a_llist_a_llist_prod_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$g (uue$ ?v0 )?v1 )?v2 )(fun_app$h (fun_app$i ?v0 ?v2 )(fun_app$j ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$g (uue$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )(?v1 A_llist_a_llist_prod_a_llist_fun$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$k (uui$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$l ?v0 ?v2 )(fun_app$h ?v1 ?v2 ))):pattern ((fun_app$h (fun_app$k (uui$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$m (uuk$ ?v0 )?v1 )?v2 )(fun_app$h (fun_app$n ?v0 ?v2 )(fun_app$o ?v1 ?v2 ))):pattern ((fun_app$h (fun_app$m (uuk$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$a (uuf$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$a ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$a (uuf$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v1 A_llist_a_llist_prod$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$l (uud$ ?v0 )?v1 )?v2 )(fun_app$h (fun_app$i ?v0 ?v2 )?v1 )):pattern ((fun_app$ (fun_app$l (uud$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$i (uuh$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$l ?v0 ?v2 )?v1 )):pattern ((fun_app$h (fun_app$i (uuh$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v1 A_llist_a_llist_prod$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$n (uuj$ ?v0 )?v1 )?v2 )(fun_app$h (fun_app$n ?v0 ?v2 )?v1 )):pattern ((fun_app$h (fun_app$n (uuj$ ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$p (uup$ ?v0 )?v1 )?v2 )(lCons$ ?v1 (fun_app$ ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$p (uup$ ?v0 )?v1 )?v2 )))):named a10 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_fun$ )(?v1 A$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$q (uuq$ ?v0 )?v1 )?v2 )(lCons$ ?v1 (fun_app$h ?v0 ?v2 ))):pattern ((fun_app$h (fun_app$q (uuq$ ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$f (uum$ ?v0 )?v1 )?v2 )(fun_app$ ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$f (uum$ ?v0 )?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist_a_llist_prod_a_llist_fun$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$k (uun$ ?v0 )?v1 )?v2 )(fun_app$ ?v0 (fun_app$h ?v1 ?v2 ))):pattern ((fun_app$h (fun_app$k (uun$ ?v0 )?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_fun$ )(?v1 A_llist_a_llist_a_llist_prod_fun$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$g (uul$ ?v0 )?v1 )?v2 )(fun_app$h ?v0 (fun_app$j ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$g (uul$ ?v0 )?v1 )?v2 )))):named a14 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_a_llist_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ )(?v2 A_llist_a_llist_prod$ ))(! (= (fun_app$h (fun_app$m (uuo$ ?v0 )?v1 )?v2 )(fun_app$h ?v0 (fun_app$o ?v1 ?v2 ))):pattern ((fun_app$h (fun_app$m (uuo$ ?v0 )?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$ (fun_app$p (fun_app$c (uua$ ?v0 )?v1 )?v2 )?v3 )(fun_app$ (fun_app$b (case_llist$ lNil$ )(fun_app$c (fun_app$r (fun_app$s (uu$ ?v0 )?v1 )?v2 )?v3 ))?v1 )):pattern ((fun_app$ (fun_app$p (fun_app$c (uua$ ?v0 )?v1 )?v2 )?v3 )))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ )(?v4 A$ )(?v5 A_llist$ ))(! (= (fun_app$ (fun_app$p (fun_app$c (fun_app$r (fun_app$s (uu$ ?v0 )?v1 )?v2 )?v3 )?v4 )?v5 )(ite (fun_app$d (fun_app$e less$ ?v2 )?v4 )(lCons$ ?v2 (fun_app$ (fun_app$a f$ ?v3 )?v1 ))(ite (fun_app$d (fun_app$e less$ ?v4 )?v2 )(lCons$ ?v4 (fun_app$ (fun_app$a f$ ?v0 )?v5 ))(lCons$ ?v4 (fun_app$ (fun_app$a f$ ?v3 )?v5 ))))):pattern ((fun_app$ (fun_app$p (fun_app$c (fun_app$r (fun_app$s (uu$ ?v0 )?v1 )?v2 )?v3 )?v4 )?v5 )))):named a17 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$ (uur$ ?v0 )?v1 )?v0 ):pattern ((fun_app$ (uur$ ?v0 )?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_a_llist_prod$ ))(! (= (fun_app$h (uus$ ?v0 )?v1 )?v0 ):pattern ((fun_app$h (uus$ ?v0 )?v1 )))):named a19 ))
(assert (! (not (mcont$ (fun_app$t (prod_lub$ lSup$ )lSup$ )(rel_prod$ lprefix$ lprefix$ )lSup$ lprefix$ (case_prod$ uub$ ))):named a20 ))
(assert (! (mcont$ (fun_app$t (prod_lub$ lSup$ )lSup$ )(rel_prod$ lprefix$ lprefix$ )lSup$ lprefix$ (case_prod$ f$ )):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$d (fun_app$e less$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$d (fun_app$e less$ ?v0 )?v2 ))):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$d (fun_app$e less$ ?v1 )?v2 ))(fun_app$d (fun_app$e less$ ?v0 )?v2 ))):named a23 ))
(assert (! (forall ((?v0 A$ ))(= (lessThan$ less$ ?v0 )(collect$ (uuc$ ?v0 )))):named a24 ))
(assert (! (forall ((?v0 A$ ))(! (= (greaterThan$ less$ ?v0 )(collect$ (fun_app$e less$ ?v0 ))):pattern ((greaterThan$ less$ ?v0 )))):named a25 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$u (fun_app$v lprefix$ lNil$ )?v0 )true ):pattern ((fun_app$u (fun_app$v lprefix$ lNil$ )?v0 )))):named a26 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$u (fun_app$v lprefix$ (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(fun_app$u (fun_app$v lprefix$ ?v1 )?v3 ))):pattern ((fun_app$u (fun_app$v lprefix$ (lCons$ ?v0 ?v1 ))(lCons$ ?v2 ?v3 ))))):named a27 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_a_llist_prod_fun$ ))(=> (and (forall ((?v6 A_llist$ ))(mcont$ ?v0 ?v1 lSup$ lprefix$ (fun_app$i ?v2 ?v6 )))(and (forall ((?v6 A_llist_a_llist_prod$ ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$l (uud$ ?v2 )?v6 )))(mcont$b ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$g (uue$ ?v2 )?v5 )))):named a28 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_a_llist_fun_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_fun$ ))(=> (and (forall ((?v6 A_llist$ ))(mcont$a ?v0 ?v1 lSup$ lprefix$ (fun_app$a ?v2 ?v6 )))(and (forall ((?v6 A_llist$ ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$a (uuf$ ?v2 )?v6 )))(mcont$a ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$f (uug$ ?v2 )?v5 )))):named a29 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_prod_a_llist_a_llist_fun_fun$ )(?v3 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v4 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v5 A_llist_a_llist_prod_a_llist_fun$ ))(=> (and (forall ((?v6 A_llist_a_llist_prod$ ))(mcont$a ?v0 ?v1 lSup$ lprefix$ (fun_app$l ?v2 ?v6 )))(and (forall ((?v6 A_llist$ ))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$i (uuh$ ?v2 )?v6 )))(mcont$ ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$k (uui$ ?v2 )?v5 )))):named a30 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist_a_llist_prod_a_llist_a_llist_prod_a_llist_fun_fun$ )(?v3 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v4 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v5 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ ))(=> (and (forall ((?v6 A_llist_a_llist_prod$ ))(mcont$ ?v0 ?v1 lSup$ lprefix$ (fun_app$n ?v2 ?v6 )))(and (forall ((?v6 A_llist_a_llist_prod$ ))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$n (uuj$ ?v2 )?v6 )))(mcont$c ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$m (uuk$ ?v2 )?v5 )))):named a31 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist_a_llist_prod_a_llist_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_a_llist_prod_fun$ ))(=> (and (mcont$ ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$b ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$g (uul$ ?v2 )?v5 )))):named a32 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_fun$ ))(=> (and (mcont$a ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$a ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$f (uum$ ?v2 )?v5 )))):named a33 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v4 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v5 A_llist_a_llist_prod_a_llist_fun$ ))(=> (and (mcont$a ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$ ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$k (uun$ ?v2 )?v5 )))):named a34 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist_a_llist_prod_a_llist_fun$ )(?v3 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v4 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v5 A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ ))(=> (and (mcont$ ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$c ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$ ?v3 ?v4 lSup$ lprefix$ (fun_app$m (uuo$ ?v2 )?v5 )))):named a35 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 A$ ))(=> (mcont$a ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$a ?v0 ?v1 lSup$ lprefix$ (fun_app$p (uup$ ?v2 )?v3 )))):named a36 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist_a_llist_prod_a_llist_fun$ )(?v3 A$ ))(=> (mcont$ ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$ ?v0 ?v1 lSup$ lprefix$ (fun_app$q (uuq$ ?v2 )?v3 )))):named a37 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist$ ))(mcont$a ?v0 ?v1 lSup$ lprefix$ (uur$ ?v2 ))):named a38 ))
(assert (! (forall ((?v0 A_llist_a_llist_prod_set_a_llist_a_llist_prod_fun$ )(?v1 A_llist_a_llist_prod_a_llist_a_llist_prod_bool_fun_fun$ )(?v2 A_llist$ ))(mcont$ ?v0 ?v1 lSup$ lprefix$ (uus$ ?v2 ))):named a39 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ )(?v2 A_llist$ ))(= (fun_app$u (fun_app$v lprefix$ ?v0 )(lCons$ ?v1 ?v2 ))(or (= ?v0 lNil$ )(exists ((?v3 A_llist$ ))(and (= ?v0 (lCons$ ?v1 ?v3 ))(fun_app$u (fun_app$v lprefix$ ?v3 )?v2 )))))):named a40 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (fun_app$u (fun_app$v lprefix$ ?v0 )?v1 )(or (exists ((?v2 A_llist$ ))(and (= ?v0 lNil$ )(= ?v1 ?v2 )))(exists ((?v2 A_llist$ )(?v3 A_llist$ )(?v4 A$ ))(and (= ?v0 (lCons$ ?v4 ?v2 ))(and (= ?v1 (lCons$ ?v4 ?v3 ))(fun_app$u (fun_app$v lprefix$ ?v2 )?v3 ))))))):named a41 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$u (fun_app$v lprefix$ (lCons$ ?v0 ?v1 ))lNil$ )false ):pattern ((lCons$ ?v0 ?v1 )))):named a42 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$u (fun_app$v lprefix$ ?v0 )?v1 )(and (forall ((?v2 A_llist$ ))(=> (and (= ?v0 lNil$ )(= ?v1 ?v2 ))false ))(forall ((?v2 A_llist$ )(?v3 A_llist$ )(?v4 A$ ))(=> (and (= ?v0 (lCons$ ?v4 ?v2 ))(and (= ?v1 (lCons$ ?v4 ?v3 ))(fun_app$u (fun_app$v lprefix$ ?v2 )?v3 )))false ))))false )):named a43 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$u (fun_app$v ?v0 ?v1 )?v2 )(forall ((?v3 A_llist$ )(?v4 A_llist$ ))(=> (fun_app$u (fun_app$v ?v0 ?v3 )?v4 )(or (exists ((?v5 A_llist$ ))(and (= ?v3 lNil$ )(= ?v4 ?v5 )))(exists ((?v5 A_llist$ )(?v6 A_llist$ )(?v7 A$ ))(and (= ?v3 (lCons$ ?v7 ?v5 ))(and (= ?v4 (lCons$ ?v7 ?v6 ))(or (fun_app$u (fun_app$v ?v0 ?v5 )?v6 )(fun_app$u (fun_app$v lprefix$ ?v5 )?v6 )))))))))(fun_app$u (fun_app$v lprefix$ ?v1 )?v2 ))):named a44 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$u (fun_app$v lprefix$ ?v0 )?v0 )):named a45 ))
(check-sat )
;(get-unsat-core )
