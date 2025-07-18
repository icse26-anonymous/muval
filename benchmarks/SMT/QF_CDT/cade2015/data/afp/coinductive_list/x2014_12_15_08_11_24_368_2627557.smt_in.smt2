;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort B_set_b_fun$ 0 )
(declare-sort A_llist_b_fun$ 0 )
(declare-sort B_a_llist_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort Bool_b_b_fun_fun$ 0 )
(declare-sort A_a_llist_b_fun_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_b_b_fun_fun$ 0 )
(declare-sort B_b_a_llist_fun_fun$ 0 )
(declare-sort Bool_a_llist_b_fun_fun$ 0 )
(declare-sort Bool_b_a_llist_fun_fun$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_a_llist_b_b_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_b_fun_fun$ 0 )
(declare-sort A_llist_b_a_llist_fun_fun$ 0 )
(declare-sort B_a_a_llist_b_fun_fun_fun$ 0 )
(declare-sort B_a_llist_a_llist_fun_fun$ 0 )
(declare-sort B_b_fun_b_a_llist_fun_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_b_fun_bool_b_b_fun_fun_fun$ 0 )
(declare-sort Bool_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_a_llist_a_llist_b_fun_fun_fun$ 0 )
(declare-sort A_llist_a_a_llist_b_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_a_llist_fun_fun$ 0 )
(declare-sort B_a_llist_fun_b_a_llist_fun_fun$ 0 )
(declare-sort A_a_llist_b_fun_fun_a_llist_b_fun_fun$ 0 )
(declare-sort A_llist_b_fun_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_llist_b_fun_bool_a_llist_b_fun_fun_fun$ 0 )
(declare-sort B_a_llist_fun_bool_b_a_llist_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ 0 )
(declare-sort A_a_llist_b_b_fun_fun_fun_a_llist_b_b_fun_fun_fun$ 0 )
(declare-sort A_llist_a_llist_fun_bool_a_llist_a_llist_fun_fun_fun$ 0 )
(declare-sort A_a_llist_a_llist_b_fun_fun_fun_a_llist_a_llist_b_fun_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun f$ (A$ )A_llist_a_llist_b_fun_fun$ )
(declare-fun uu$ (A_llist$ )A_a_llist_b_fun_fun$ )
(declare-fun bot$ ()B$ )
(declare-fun lub$ ()B_set_b_fun$ )
(declare-fun ord$ ()B_b_bool_fun_fun$ )
(declare-fun uua$ ()A_llist_b_fun$ )
(declare-fun uub$ (B_b_a_llist_fun_fun$ )B_b_a_llist_fun_fun$ )
(declare-fun uuc$ (B_b_a_llist_fun_fun$ )B_b_fun_b_a_llist_fun_fun$ )
(declare-fun uud$ (B_a_llist_a_llist_fun_fun$ )A_llist_b_a_llist_fun_fun$ )
(declare-fun uue$ (B_a_llist_a_llist_fun_fun$ )B_a_llist_fun_b_a_llist_fun_fun$ )
(declare-fun uuf$ (A_llist_a_llist_a_llist_fun_fun$ )A_llist_a_llist_a_llist_fun_fun$ )
(declare-fun uug$ (A_llist_a_llist_a_llist_fun_fun$ )A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uuh$ (A_llist_b_a_llist_fun_fun$ )B_a_llist_a_llist_fun_fun$ )
(declare-fun uui$ (A_llist_b_a_llist_fun_fun$ )A_llist_b_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uuj$ (A_a_llist_b_b_fun_fun_fun$ )B_a_a_llist_b_fun_fun_fun$ )
(declare-fun uuk$ (B_b_fun$ )A_a_llist_b_b_fun_fun_fun_a_llist_b_b_fun_fun_fun$ )
(declare-fun uul$ (A_a_llist_a_llist_b_fun_fun_fun$ )A_llist_a_a_llist_b_fun_fun_fun$ )
(declare-fun uum$ (A_llist_b_fun$ )A_a_llist_a_llist_b_fun_fun_fun_a_llist_a_llist_b_fun_fun_fun$ )
(declare-fun uun$ (B_a_llist_fun$ )B_b_fun_b_a_llist_fun_fun$ )
(declare-fun uuo$ (A_llist_a_llist_fun$ )B_a_llist_fun_b_a_llist_fun_fun$ )
(declare-fun uup$ (A_llist_a_llist_fun$ )A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uuq$ (B_a_llist_fun$ )A_llist_b_fun_a_llist_a_llist_fun_fun$ )
(declare-fun uur$ (A$ )A_llist_b_fun$ )
(declare-fun uus$ (B_b_fun$ )B_b_fun_bool_b_b_fun_fun_fun$ )
(declare-fun uut$ (B_a_llist_fun$ )B_a_llist_fun_bool_b_a_llist_fun_fun_fun$ )
(declare-fun uuu$ (A_llist_a_llist_fun$ )A_llist_a_llist_fun_bool_a_llist_a_llist_fun_fun_fun$ )
(declare-fun uuv$ (A_llist_b_fun$ )A_llist_b_fun_bool_a_llist_b_fun_fun_fun$ )
(declare-fun uuw$ ()B_b_fun$ )
(declare-fun uux$ ()A_llist_a_llist_fun$ )
(declare-fun uuy$ (A_llist$ )A_llist_bool_fun$ )
(declare-fun uuz$ (A_llist$ A_llist$ )A_llist_bool_fun$ )
(declare-fun lSup$ ()A_llist_set_a_llist_fun$ )
(declare-fun mcont$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ B_set_b_fun$ B_b_bool_fun_fun$ A_llist_b_fun$ )Bool )
(declare-fun mcont$a (B_set_b_fun$ B_b_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ B_a_llist_fun$ )Bool )
(declare-fun mcont$b (B_set_b_fun$ B_b_bool_fun_fun$ B_set_b_fun$ B_b_bool_fun_fun$ B_b_fun$ )Bool )
(declare-fun mcont$c (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$ )Bool )
(declare-fun collect$ (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_b_fun$ A_llist$ )B$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun fun_app$a (A_a_llist_b_fun_fun_a_llist_b_fun_fun$ A_a_llist_b_fun_fun$ )A_llist_b_fun$ )
(declare-fun fun_app$b (A_llist_a_llist_b_fun_fun$ A_llist$ )A_llist_b_fun$ )
(declare-fun fun_app$c (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$d (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$e (A_a_llist_b_fun_fun$ A$ )A_llist_b_fun$ )
(declare-fun fun_app$f (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$g (A_llist_a_llist_fun_a_llist_a_llist_fun_fun$ A_llist_a_llist_fun$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$h (A_llist_a_llist_a_llist_fun_fun$ A_llist$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$i (A_llist_b_fun_a_llist_a_llist_fun_fun$ A_llist_b_fun$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$j (B_a_llist_fun$ B$ )A_llist$ )
(declare-fun fun_app$k (A_llist_b_a_llist_fun_fun$ A_llist$ )B_a_llist_fun$ )
(declare-fun fun_app$l (B_a_llist_fun_b_a_llist_fun_fun$ B_a_llist_fun$ )B_a_llist_fun$ )
(declare-fun fun_app$m (B_a_llist_a_llist_fun_fun$ B$ )A_llist_a_llist_fun$ )
(declare-fun fun_app$n (B_b_fun_b_a_llist_fun_fun$ B_b_fun$ )B_a_llist_fun$ )
(declare-fun fun_app$o (B_b_a_llist_fun_fun$ B$ )B_a_llist_fun$ )
(declare-fun fun_app$p (B_b_fun$ B$ )B$ )
(declare-fun fun_app$q (A_llist_a_a_llist_b_fun_fun_fun$ A_llist$ )A_a_llist_b_fun_fun$ )
(declare-fun fun_app$r (A_a_llist_a_llist_b_fun_fun_fun$ A$ )A_llist_a_llist_b_fun_fun$ )
(declare-fun fun_app$s (B_a_a_llist_b_fun_fun_fun$ B$ )A_a_llist_b_fun_fun$ )
(declare-fun fun_app$t (A_llist_b_b_fun_fun$ A_llist$ )B_b_fun$ )
(declare-fun fun_app$u (A_a_llist_b_b_fun_fun_fun$ A$ )A_llist_b_b_fun_fun$ )
(declare-fun fun_app$v (A_a_llist_a_llist_b_fun_fun_fun_a_llist_a_llist_b_fun_fun_fun$ A_a_llist_a_llist_b_fun_fun_fun$ )A_llist_a_llist_b_fun_fun$ )
(declare-fun fun_app$w (A_a_llist_b_b_fun_fun_fun_a_llist_b_b_fun_fun_fun$ A_a_llist_b_b_fun_fun_fun$ )A_llist_b_b_fun_fun$ )
(declare-fun fun_app$x (Bool_a_llist_a_llist_fun_fun$ Bool )A_llist_a_llist_fun$ )
(declare-fun fun_app$y (A_llist_a_llist_fun_bool_a_llist_a_llist_fun_fun_fun$ A_llist_a_llist_fun$ )Bool_a_llist_a_llist_fun_fun$ )
(declare-fun fun_app$z (Bool_a_llist_b_fun_fun$ Bool )A_llist_b_fun$ )
(declare-fun fun_app$aa (A_llist_b_fun_bool_a_llist_b_fun_fun_fun$ A_llist_b_fun$ )Bool_a_llist_b_fun_fun$ )
(declare-fun fun_app$ab (Bool_b_a_llist_fun_fun$ Bool )B_a_llist_fun$ )
(declare-fun fun_app$ac (B_a_llist_fun_bool_b_a_llist_fun_fun_fun$ B_a_llist_fun$ )Bool_b_a_llist_fun_fun$ )
(declare-fun fun_app$ad (Bool_b_b_fun_fun$ Bool )B_b_fun$ )
(declare-fun fun_app$ae (B_b_fun_bool_b_b_fun_fun_fun$ B_b_fun$ )Bool_b_b_fun_fun$ )
(declare-fun fun_app$af (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$ag (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$ah (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun case_llist$ (B$ )A_a_llist_b_fun_fun_a_llist_b_fun_fun$ )
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ uua$ ?v0 )(fun_app$ (fun_app$a (case_llist$ bot$ )(uu$ ?v0 ))?v0 )):pattern ((fun_app$ uua$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (fun_app$ (uur$ ?v0 )?v1 )(fun_app$ (fun_app$b (f$ ?v0 )?v1 )(lCons$ ?v0 ?v1 ))):pattern ((fun_app$ (uur$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$c (uuy$ ?v0 )?v1 )(and (fun_app$c (fun_app$d lprefix$ ?v1 )?v0 )(lfinite$ ?v1 ))):pattern ((fun_app$c (uuy$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ )(?v2 A_llist$ ))(! (= (fun_app$ (fun_app$e (uu$ ?v0 )?v1 )?v2 )(fun_app$ (fun_app$b (f$ ?v1 )?v2 )?v0 )):pattern ((fun_app$ (fun_app$e (uu$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_fun_fun$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$g (uug$ ?v0 )?v1 )?v2 )(fun_app$f (fun_app$h ?v0 ?v2 )(fun_app$f ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$g (uug$ ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_b_a_llist_fun_fun$ )(?v1 A_llist_b_fun$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$i (uui$ ?v0 )?v1 )?v2 )(fun_app$j (fun_app$k ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$i (uui$ ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 B_a_llist_a_llist_fun_fun$ )(?v1 B_a_llist_fun$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$l (uue$ ?v0 )?v1 )?v2 )(fun_app$f (fun_app$m ?v0 ?v2 )(fun_app$j ?v1 ?v2 ))):pattern ((fun_app$j (fun_app$l (uue$ ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 B_b_a_llist_fun_fun$ )(?v1 B_b_fun$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$n (uuc$ ?v0 )?v1 )?v2 )(fun_app$j (fun_app$o ?v0 ?v2 )(fun_app$p ?v1 ?v2 ))):pattern ((fun_app$j (fun_app$n (uuc$ ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$h (uuf$ ?v0 )?v1 )?v2 )(fun_app$f (fun_app$h ?v0 ?v2 )?v1 )):pattern ((fun_app$f (fun_app$h (uuf$ ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_llist_b_a_llist_fun_fun$ )(?v1 B$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$m (uuh$ ?v0 )?v1 )?v2 )(fun_app$j (fun_app$k ?v0 ?v2 )?v1 )):pattern ((fun_app$f (fun_app$m (uuh$ ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 B_a_llist_a_llist_fun_fun$ )(?v1 A_llist$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$k (uud$ ?v0 )?v1 )?v2 )(fun_app$f (fun_app$m ?v0 ?v2 )?v1 )):pattern ((fun_app$j (fun_app$k (uud$ ?v0 )?v1 )?v2 )))):named a10 ))
(assert (! (forall ((?v0 B_b_a_llist_fun_fun$ )(?v1 B$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$o (uub$ ?v0 )?v1 )?v2 )(fun_app$j (fun_app$o ?v0 ?v2 )?v1 )):pattern ((fun_app$j (fun_app$o (uub$ ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$c (uuz$ ?v0 ?v1 )?v2 )(and (fun_app$c (fun_app$d lprefix$ ?v2 )?v1 )(and (fun_app$c (fun_app$d lprefix$ ?v0 )?v2 )(lfinite$ ?v2 )))):pattern ((fun_app$c (uuz$ ?v0 ?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$g (uup$ ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$f ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$g (uup$ ?v0 )?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 B_a_llist_fun$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$l (uuo$ ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$j ?v1 ?v2 ))):pattern ((fun_app$j (fun_app$l (uuo$ ?v0 )?v1 )?v2 )))):named a14 ))
(assert (! (forall ((?v0 B_a_llist_fun$ )(?v1 A_llist_b_fun$ )(?v2 A_llist$ ))(! (= (fun_app$f (fun_app$i (uuq$ ?v0 )?v1 )?v2 )(fun_app$j ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$i (uuq$ ?v0 )?v1 )?v2 )))):named a15 ))
(assert (! (forall ((?v0 B_a_llist_fun$ )(?v1 B_b_fun$ )(?v2 B$ ))(! (= (fun_app$j (fun_app$n (uun$ ?v0 )?v1 )?v2 )(fun_app$j ?v0 (fun_app$p ?v1 ?v2 ))):pattern ((fun_app$j (fun_app$n (uun$ ?v0 )?v1 )?v2 )))):named a16 ))
(assert (! (forall ((?v0 A_a_llist_a_llist_b_fun_fun_fun$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$ (fun_app$e (fun_app$q (uul$ ?v0 )?v1 )?v2 )?v3 )(fun_app$ (fun_app$b (fun_app$r ?v0 ?v2 )?v3 )?v1 )):pattern ((fun_app$ (fun_app$e (fun_app$q (uul$ ?v0 )?v1 )?v2 )?v3 )))):named a17 ))
(assert (! (forall ((?v0 A_a_llist_b_b_fun_fun_fun$ )(?v1 B$ )(?v2 A$ )(?v3 A_llist$ ))(! (= (fun_app$ (fun_app$e (fun_app$s (uuj$ ?v0 )?v1 )?v2 )?v3 )(fun_app$p (fun_app$t (fun_app$u ?v0 ?v2 )?v3 )?v1 )):pattern ((fun_app$ (fun_app$e (fun_app$s (uuj$ ?v0 )?v1 )?v2 )?v3 )))):named a18 ))
(assert (! (forall ((?v0 A_llist_b_fun$ )(?v1 A_a_llist_a_llist_b_fun_fun_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(! (= (fun_app$ (fun_app$b (fun_app$v (uum$ ?v0 )?v1 )?v2 )?v3 )(fun_app$ (fun_app$a (case_llist$ (fun_app$ ?v0 ?v3 ))(fun_app$q (uul$ ?v1 )?v3 ))?v2 )):pattern ((fun_app$ (fun_app$b (fun_app$v (uum$ ?v0 )?v1 )?v2 )?v3 )))):named a19 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_a_llist_b_b_fun_fun_fun$ )(?v2 A_llist$ )(?v3 B$ ))(! (= (fun_app$p (fun_app$t (fun_app$w (uuk$ ?v0 )?v1 )?v2 )?v3 )(fun_app$ (fun_app$a (case_llist$ (fun_app$p ?v0 ?v3 ))(fun_app$s (uuj$ ?v1 )?v3 ))?v2 )):pattern ((fun_app$p (fun_app$t (fun_app$w (uuk$ ?v0 )?v1 )?v2 )?v3 )))):named a20 ))
(assert (! (forall ((?v0 A_llist_a_llist_fun$ )(?v1 A_llist_a_llist_fun$ )(?v2 Bool )(?v3 A_llist$ ))(! (= (fun_app$f (fun_app$x (fun_app$y (uuu$ ?v0 )?v1 )?v2 )?v3 )(ite ?v2 (fun_app$f ?v0 ?v3 )(fun_app$f ?v1 ?v3 ))):pattern ((fun_app$f (fun_app$x (fun_app$y (uuu$ ?v0 )?v1 )?v2 )?v3 )))):named a21 ))
(assert (! (forall ((?v0 A_llist_b_fun$ )(?v1 A_llist_b_fun$ )(?v2 Bool )(?v3 A_llist$ ))(! (= (fun_app$ (fun_app$z (fun_app$aa (uuv$ ?v0 )?v1 )?v2 )?v3 )(ite ?v2 (fun_app$ ?v0 ?v3 )(fun_app$ ?v1 ?v3 ))):pattern ((fun_app$ (fun_app$z (fun_app$aa (uuv$ ?v0 )?v1 )?v2 )?v3 )))):named a22 ))
(assert (! (forall ((?v0 B_a_llist_fun$ )(?v1 B_a_llist_fun$ )(?v2 Bool )(?v3 B$ ))(! (= (fun_app$j (fun_app$ab (fun_app$ac (uut$ ?v0 )?v1 )?v2 )?v3 )(ite ?v2 (fun_app$j ?v0 ?v3 )(fun_app$j ?v1 ?v3 ))):pattern ((fun_app$j (fun_app$ab (fun_app$ac (uut$ ?v0 )?v1 )?v2 )?v3 )))):named a23 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun$ )(?v2 Bool )(?v3 B$ ))(! (= (fun_app$p (fun_app$ad (fun_app$ae (uus$ ?v0 )?v1 )?v2 )?v3 )(ite ?v2 (fun_app$p ?v0 ?v3 )(fun_app$p ?v1 ?v3 ))):pattern ((fun_app$p (fun_app$ad (fun_app$ae (uus$ ?v0 )?v1 )?v2 )?v3 )))):named a24 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$f uux$ ?v0 )?v0 ):pattern ((fun_app$f uux$ ?v0 )))):named a25 ))
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$p uuw$ ?v0 )?v0 ):pattern ((fun_app$p uuw$ ?v0 )))):named a26 ))
(assert (! (not (mcont$ lSup$ lprefix$ lub$ ord$ uua$ )):named a27 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$c (fun_app$d lprefix$ ?v0 )?v0 )):named a28 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$c (fun_app$d lprefix$ ?v0 )?v0 )):named a29 ))
(assert (! (forall ((?v0 B$ ))(fun_app$af (fun_app$ag ord$ bot$ )?v0 )):named a30 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_b_a_llist_fun_fun$ )(?v3 B_set_b_fun$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_b_fun$ ))(=> (and (forall ((?v6 B$ ))(mcont$a ?v0 ?v1 lSup$ lprefix$ (fun_app$o ?v2 ?v6 )))(and (forall ((?v6 B$ ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$o (uub$ ?v2 )?v6 )))(mcont$b ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$n (uuc$ ?v2 )?v5 )))):named a31 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 B_a_llist_a_llist_fun_fun$ )(?v3 B_set_b_fun$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_a_llist_fun$ ))(=> (and (forall ((?v6 B$ ))(mcont$c ?v0 ?v1 lSup$ lprefix$ (fun_app$m ?v2 ?v6 )))(and (forall ((?v6 A_llist$ ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$k (uud$ ?v2 )?v6 )))(mcont$a ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$l (uue$ ?v2 )?v5 )))):named a32 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_a_llist_fun_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_fun$ ))(=> (and (forall ((?v6 A_llist$ ))(mcont$c ?v0 ?v1 lSup$ lprefix$ (fun_app$h ?v2 ?v6 )))(and (forall ((?v6 A_llist$ ))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$h (uuf$ ?v2 )?v6 )))(mcont$c ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$g (uug$ ?v2 )?v5 )))):named a33 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A_llist_b_a_llist_fun_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_b_fun$ ))(=> (and (forall ((?v6 A_llist$ ))(mcont$a ?v0 ?v1 lSup$ lprefix$ (fun_app$k ?v2 ?v6 )))(and (forall ((?v6 B$ ))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$m (uuh$ ?v2 )?v6 )))(mcont$ ?v3 ?v4 ?v0 ?v1 ?v5 )))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$i (uui$ ?v2 )?v5 )))):named a34 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 B_b_fun$ )(?v5 A_a_llist_b_b_fun_fun_fun$ )(?v6 A_llist$ ))(=> (and (mcont$b ?v0 ?v1 ?v2 ?v3 ?v4 )(forall ((?v7 A$ )(?v8 A_llist$ ))(mcont$b ?v0 ?v1 ?v2 ?v3 (fun_app$t (fun_app$u ?v5 ?v7 )?v8 ))))(mcont$b ?v0 ?v1 ?v2 ?v3 (fun_app$t (fun_app$w (uuk$ ?v4 )?v5 )?v6 )))):named a35 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 A_llist_b_fun$ )(?v5 A_a_llist_a_llist_b_fun_fun_fun$ )(?v6 A_llist$ ))(=> (and (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4 )(forall ((?v7 A$ )(?v8 A_llist$ ))(mcont$ ?v0 ?v1 ?v2 ?v3 (fun_app$b (fun_app$r ?v5 ?v7 )?v8 ))))(mcont$ ?v0 ?v1 ?v2 ?v3 (fun_app$b (fun_app$v (uum$ ?v4 )?v5 )?v6 )))):named a36 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_a_llist_fun$ )(?v3 B_set_b_fun$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_b_fun$ ))(=> (and (mcont$a ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$b ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$n (uun$ ?v2 )?v5 )))):named a37 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 B_set_b_fun$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_a_llist_fun$ ))(=> (and (mcont$c ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$a ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$a ?v3 ?v4 lSup$ lprefix$ (fun_app$l (uuo$ ?v2 )?v5 )))):named a38 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_a_llist_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_a_llist_fun$ ))(=> (and (mcont$c ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$c ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$g (uup$ ?v2 )?v5 )))):named a39 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_a_llist_fun$ )(?v3 A_llist_set_a_llist_fun$ )(?v4 A_llist_a_llist_bool_fun_fun$ )(?v5 A_llist_b_fun$ ))(=> (and (mcont$a ?v0 ?v1 lSup$ lprefix$ ?v2 )(mcont$ ?v3 ?v4 ?v0 ?v1 ?v5 ))(mcont$c ?v3 ?v4 lSup$ lprefix$ (fun_app$i (uuq$ ?v2 )?v5 )))):named a40 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(fun_app$c (fun_app$d lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a41 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(fun_app$c (fun_app$d lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a42 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(fun_app$c (fun_app$d lprefix$ ?v2 )?v1 ))(or (fun_app$c (fun_app$d lprefix$ ?v0 )?v2 )(fun_app$c (fun_app$d lprefix$ ?v2 )?v0 )))):named a43 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(fun_app$c (fun_app$d lprefix$ ?v1 )?v2 ))(fun_app$c (fun_app$d lprefix$ ?v0 )?v2 ))):named a44 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(fun_app$c (fun_app$d lprefix$ ?v1 )?v2 ))(fun_app$c (fun_app$d lprefix$ ?v0 )?v2 ))):named a45 ))
(assert (! (forall ((?v0 A$ ))(mcont$ lSup$ lprefix$ lub$ ord$ (uur$ ?v0 ))):named a46 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 B_b_fun$ )(?v5 B_b_fun$ )(?v6 Bool ))(=> (and (mcont$b ?v0 ?v1 ?v2 ?v3 ?v4 )(mcont$b ?v0 ?v1 ?v2 ?v3 ?v5 ))(mcont$b ?v0 ?v1 ?v2 ?v3 (fun_app$ad (fun_app$ae (uus$ ?v4 )?v5 )?v6 )))):named a47 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 B_a_llist_fun$ )(?v5 B_a_llist_fun$ )(?v6 Bool ))(=> (and (mcont$a ?v0 ?v1 ?v2 ?v3 ?v4 )(mcont$a ?v0 ?v1 ?v2 ?v3 ?v5 ))(mcont$a ?v0 ?v1 ?v2 ?v3 (fun_app$ab (fun_app$ac (uut$ ?v4 )?v5 )?v6 )))):named a48 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 A_llist_a_llist_fun$ )(?v5 A_llist_a_llist_fun$ )(?v6 Bool ))(=> (and (mcont$c ?v0 ?v1 ?v2 ?v3 ?v4 )(mcont$c ?v0 ?v1 ?v2 ?v3 ?v5 ))(mcont$c ?v0 ?v1 ?v2 ?v3 (fun_app$x (fun_app$y (uuu$ ?v4 )?v5 )?v6 )))):named a49 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 A_llist_b_fun$ )(?v5 A_llist_b_fun$ )(?v6 Bool ))(=> (and (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4 )(mcont$ ?v0 ?v1 ?v2 ?v3 ?v5 ))(mcont$ ?v0 ?v1 ?v2 ?v3 (fun_app$z (fun_app$aa (uuv$ ?v4 )?v5 )?v6 )))):named a50 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ ))(mcont$b ?v0 ?v1 ?v0 ?v1 uuw$ )):named a51 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ ))(mcont$c ?v0 ?v1 ?v0 ?v1 uux$ )):named a52 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 B_b_fun$ )(?v5 B$ )(?v6 B$ ))(=> (and (mcont$b ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$af (fun_app$ag ?v1 ?v5 )?v6 ))(fun_app$af (fun_app$ag ?v3 (fun_app$p ?v4 ?v5 ))(fun_app$p ?v4 ?v6 )))):named a53 ))
(assert (! (forall ((?v0 B_set_b_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 B_a_llist_fun$ )(?v5 B$ )(?v6 B$ ))(=> (and (mcont$a ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$af (fun_app$ag ?v1 ?v5 )?v6 ))(fun_app$c (fun_app$d ?v3 (fun_app$j ?v4 ?v5 ))(fun_app$j ?v4 ?v6 )))):named a54 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist_a_llist_bool_fun_fun$ )(?v4 A_llist_a_llist_fun$ )(?v5 A_llist$ )(?v6 A_llist$ ))(=> (and (mcont$c ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$c (fun_app$d ?v1 ?v5 )?v6 ))(fun_app$c (fun_app$d ?v3 (fun_app$f ?v4 ?v5 ))(fun_app$f ?v4 ?v6 )))):named a55 ))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$ )(?v1 A_llist_a_llist_bool_fun_fun$ )(?v2 B_set_b_fun$ )(?v3 B_b_bool_fun_fun$ )(?v4 A_llist_b_fun$ )(?v5 A_llist$ )(?v6 A_llist$ ))(=> (and (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4 )(fun_app$c (fun_app$d ?v1 ?v5 )?v6 ))(fun_app$af (fun_app$ag ?v3 (fun_app$ ?v4 ?v5 ))(fun_app$ ?v4 ?v6 )))):named a56 ))
(assert (! (forall ((?v0 A_llist$ ))(= (fun_app$ah lSup$ (collect$ (uuy$ ?v0 )))?v0 )):named a57 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$c (fun_app$d lprefix$ ?v0 )?v1 )(lfinite$ ?v0 ))(= (fun_app$ah lSup$ (collect$ (uuz$ ?v0 ?v1 )))?v1 ))):named a58 ))
(check-sat )
;(get-unsat-core )
