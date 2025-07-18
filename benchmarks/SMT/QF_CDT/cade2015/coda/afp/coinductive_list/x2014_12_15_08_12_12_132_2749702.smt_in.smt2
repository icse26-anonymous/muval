;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_set_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_set_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_set_a_fun$ 0 )
(declare-sort A_a_llist_fun$ 0 )
(declare-sort A_llist_a_fun$ 0 )
(declare-sort A_set_set_set$ 0 )
(declare-sort A_set_bool_fun$ 0 )
(declare-sort A_a_set_set_fun$ 0 )
(declare-sort A_llist_set_set$ 0 )
(declare-sort A_set_a_set_fun$ 0 )
(declare-sort A_set_set_a_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort A_set_a_llist_fun$ 0 )
(declare-sort A_set_set_set_set$ 0 )
(declare-sort A_set_set_bool_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_set_set_set$ 0 )
(declare-sort A_llist_set_bool_fun$ 0 )
(declare-sort A_set_a_set_bool_fun_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort A_set_set_a_set_set_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun y$ ()A_llist_set$ )
(declare-fun sup$ (A_set_set$ )A_set$ )
(declare-fun lSup$ (A_llist_set$ )A_llist$ )
(declare-fun lset$ ()A_llist_a_set_fun$ )
(declare-fun sup$a (A_set_set_set_set$ )A_set_set_set$ )
(declare-fun sup$b (A_llist_set_set_set$ )A_llist_set_set$ )
(declare-fun sup$c (A_llist_set_set$ )A_llist_set$ )
(declare-fun sup$d (A_set_set_set$ )A_set_set$ )
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ )A_llist_set_bool_fun$ )
(declare-fun image$ (A_llist_a_set_fun$ A_llist_set$ )A_set_set$ )
(declare-fun chain$a (A_set_a_set_bool_fun_fun$ )A_set_set_bool_fun$ )
(declare-fun chain$b (A_a_bool_fun_fun$ )A_set_bool_fun$ )
(declare-fun chain$c (A_set_set_a_set_set_bool_fun_fun$ A_set_set_set$ )Bool )
(declare-fun image$a (A_a_fun$ )A_set_a_set_fun$ )
(declare-fun image$b (A_llist_a_fun$ A_llist_set$ )A_set$ )
(declare-fun image$c (A_a_llist_fun$ A_set$ )A_llist_set$ )
(declare-fun image$d (A_a_set_fun$ A_set$ )A_set_set$ )
(declare-fun image$e (A_set_a_fun$ A_set_set$ )A_set$ )
(declare-fun image$f (A_llist_a_llist_fun$ A_llist_set$ )A_llist_set$ )
(declare-fun image$g (A_set_a_llist_fun$ A_set_set$ )A_llist_set$ )
(declare-fun image$h (A_set_a_set_fun$ A_set_set$ )A_set_set$ )
(declare-fun image$i (A_a_set_set_fun$ A_set$ )A_set_set_set$ )
(declare-fun image$j (A_set_set_a_fun$ A_set_set_set$ )A_set$ )
(declare-fun member$ (A_llist$ )A_llist_set_bool_fun$ )
(declare-fun fun_app$ (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun lprefix$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun member$a (A_set_set$ A_set_set_set$ )Bool )
(declare-fun member$b (A_set_set_set$ A_set_set_set_set$ )Bool )
(declare-fun member$c (A_llist_set$ A_llist_set_set$ )Bool )
(declare-fun member$d (A_llist_set_set$ A_llist_set_set_set$ )Bool )
(declare-fun member$e (A_set$ )A_set_set_bool_fun$ )
(declare-fun member$f (A$ )A_set_bool_fun$ )
(declare-fun fun_app$a (A_llist_set_bool_fun$ A_llist_set$ )Bool )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (A_set_set_bool_fun$ A_set_set$ )Bool )
(declare-fun fun_app$e (A_set_bool_fun$ A_set$ )Bool )
(declare-fun fun_app$f (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$g (A_a_fun$ A$ )A$ )
(declare-fun fun_app$h (A_set_a_set_fun$ A_set$ )A_set$ )
(declare-fun fun_app$i (A_llist_a_fun$ A_llist$ )A$ )
(declare-fun fun_app$j (A_a_llist_fun$ A$ )A_llist$ )
(declare-fun fun_app$k (A_a_set_fun$ A$ )A_set$ )
(declare-fun fun_app$l (A_set_a_fun$ A_set$ )A$ )
(declare-fun fun_app$m (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun fun_app$n (A_set_a_llist_fun$ A_set$ )A_llist$ )
(declare-fun fun_app$o (A_a_set_set_fun$ A$ )A_set_set$ )
(declare-fun fun_app$p (A_set_a_set_bool_fun_fun$ A_set$ )A_set_bool_fun$ )
(declare-fun fun_app$q (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$r (A_set_set_a_set_set_bool_fun_fun$ A_set_set$ )A_set_set_bool_fun$ )
(declare-fun fun_app$s (A_set_set_a_fun$ A_set_set$ )A$ )
(assert (! (not (= (fun_app$ lset$ (lSup$ y$ ))(sup$ (image$ lset$ y$ )))):named a0 ))
(assert (! (fun_app$a (chain$ lprefix$ )y$ ):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$b (fun_app$c lprefix$ ?v0 )?v0 )):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$b (fun_app$c lprefix$ ?v0 )?v0 )):named a3 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (fun_app$a (chain$ lprefix$ )?v0 )(forall ((?v2 A_llist$ ))(=> (fun_app$a (member$ ?v2 )?v0 )(fun_app$b (fun_app$c lprefix$ ?v2 )?v1 ))))(fun_app$b (fun_app$c lprefix$ (lSup$ ?v0 ))?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (fun_app$a (chain$ lprefix$ )?v0 )(forall ((?v2 A_llist$ ))(=> (fun_app$a (member$ ?v2 )?v0 )(fun_app$b (fun_app$c lprefix$ ?v2 )?v1 ))))(fun_app$b (fun_app$c lprefix$ (lSup$ ?v0 ))?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (fun_app$a (chain$ lprefix$ )?v0 )(fun_app$a (member$ ?v1 )?v0 ))(fun_app$b (fun_app$c lprefix$ ?v1 )(lSup$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist$ ))(=> (and (fun_app$a (chain$ lprefix$ )?v0 )(fun_app$a (member$ ?v1 )?v0 ))(fun_app$b (fun_app$c lprefix$ ?v1 )(lSup$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$b (fun_app$c lprefix$ ?v0 )?v1 )(fun_app$b (fun_app$c lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (fun_app$b (fun_app$c lprefix$ ?v0 )?v1 )(fun_app$b (fun_app$c lprefix$ ?v1 )?v0 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c lprefix$ ?v0 )?v1 )(fun_app$b (fun_app$c lprefix$ ?v2 )?v1 ))(or (fun_app$b (fun_app$c lprefix$ ?v0 )?v2 )(fun_app$b (fun_app$c lprefix$ ?v2 )?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c lprefix$ ?v0 )?v1 )(fun_app$b (fun_app$c lprefix$ ?v1 )?v2 ))(fun_app$b (fun_app$c lprefix$ ?v0 )?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c lprefix$ ?v0 )?v1 )(fun_app$b (fun_app$c lprefix$ ?v1 )?v2 ))(fun_app$b (fun_app$c lprefix$ ?v0 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_set_set_set_set$ )(?v1 A_set_set_bool_fun$ ))(= (exists ((?v2 A_set_set$ ))(and (member$a ?v2 (sup$a ?v0 ))(fun_app$d ?v1 ?v2 )))(exists ((?v2 A_set_set_set$ ))(and (member$b ?v2 ?v0 )(exists ((?v3 A_set_set$ ))(and (member$a ?v3 ?v2 )(fun_app$d ?v1 ?v3 ))))))):named a13 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ )(?v1 A_llist_set_bool_fun$ ))(= (exists ((?v2 A_llist_set$ ))(and (member$c ?v2 (sup$b ?v0 ))(fun_app$a ?v1 ?v2 )))(exists ((?v2 A_llist_set_set$ ))(and (member$d ?v2 ?v0 )(exists ((?v3 A_llist_set$ ))(and (member$c ?v3 ?v2 )(fun_app$a ?v1 ?v3 ))))))):named a14 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_bool_fun$ ))(= (exists ((?v2 A_llist$ ))(and (fun_app$a (member$ ?v2 )(sup$c ?v0 ))(fun_app$b ?v1 ?v2 )))(exists ((?v2 A_llist_set$ ))(and (member$c ?v2 ?v0 )(exists ((?v3 A_llist$ ))(and (fun_app$a (member$ ?v3 )?v2 )(fun_app$b ?v1 ?v3 ))))))):named a15 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_bool_fun$ ))(= (exists ((?v2 A_set$ ))(and (fun_app$d (member$e ?v2 )(sup$d ?v0 ))(fun_app$e ?v1 ?v2 )))(exists ((?v2 A_set_set$ ))(and (member$a ?v2 ?v0 )(exists ((?v3 A_set$ ))(and (fun_app$d (member$e ?v3 )?v2 )(fun_app$e ?v1 ?v3 ))))))):named a16 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_bool_fun$ ))(= (exists ((?v2 A$ ))(and (fun_app$e (member$f ?v2 )(sup$ ?v0 ))(fun_app$f ?v1 ?v2 )))(exists ((?v2 A_set$ ))(and (fun_app$d (member$e ?v2 )?v0 )(exists ((?v3 A$ ))(and (fun_app$e (member$f ?v3 )?v2 )(fun_app$f ?v1 ?v3 ))))))):named a17 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set_set_set$ ))(= (member$a ?v0 (sup$a ?v1 ))(exists ((?v2 A_set_set_set$ ))(and (member$b ?v2 ?v1 )(member$a ?v0 ?v2 ))))):named a18 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set_set_set$ ))(= (member$c ?v0 (sup$b ?v1 ))(exists ((?v2 A_llist_set_set$ ))(and (member$d ?v2 ?v1 )(member$c ?v0 ?v2 ))))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_set_set$ ))(= (fun_app$a (member$ ?v0 )(sup$c ?v1 ))(exists ((?v2 A_llist_set$ ))(and (member$c ?v2 ?v1 )(fun_app$a (member$ ?v0 )?v2 ))))):named a20 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set_set$ ))(= (fun_app$d (member$e ?v0 )(sup$d ?v1 ))(exists ((?v2 A_set_set$ ))(and (member$a ?v2 ?v1 )(fun_app$d (member$e ?v0 )?v2 ))))):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set_set$ ))(= (fun_app$e (member$f ?v0 )(sup$ ?v1 ))(exists ((?v2 A_set$ ))(and (fun_app$d (member$e ?v2 )?v1 )(fun_app$e (member$f ?v0 )?v2 ))))):named a22 ))
(assert (! (forall ((?v0 A_set_set_set_set$ )(?v1 A_set_set_bool_fun$ ))(= (forall ((?v2 A_set_set$ ))(=> (member$a ?v2 (sup$a ?v0 ))(fun_app$d ?v1 ?v2 )))(forall ((?v2 A_set_set_set$ ))(=> (member$b ?v2 ?v0 )(forall ((?v3 A_set_set$ ))(=> (member$a ?v3 ?v2 )(fun_app$d ?v1 ?v3 ))))))):named a23 ))
(assert (! (forall ((?v0 A_llist_set_set_set$ )(?v1 A_llist_set_bool_fun$ ))(= (forall ((?v2 A_llist_set$ ))(=> (member$c ?v2 (sup$b ?v0 ))(fun_app$a ?v1 ?v2 )))(forall ((?v2 A_llist_set_set$ ))(=> (member$d ?v2 ?v0 )(forall ((?v3 A_llist_set$ ))(=> (member$c ?v3 ?v2 )(fun_app$a ?v1 ?v3 ))))))):named a24 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_bool_fun$ ))(= (forall ((?v2 A_llist$ ))(=> (fun_app$a (member$ ?v2 )(sup$c ?v0 ))(fun_app$b ?v1 ?v2 )))(forall ((?v2 A_llist_set$ ))(=> (member$c ?v2 ?v0 )(forall ((?v3 A_llist$ ))(=> (fun_app$a (member$ ?v3 )?v2 )(fun_app$b ?v1 ?v3 ))))))):named a25 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_bool_fun$ ))(= (forall ((?v2 A_set$ ))(=> (fun_app$d (member$e ?v2 )(sup$d ?v0 ))(fun_app$e ?v1 ?v2 )))(forall ((?v2 A_set_set$ ))(=> (member$a ?v2 ?v0 )(forall ((?v3 A_set$ ))(=> (fun_app$d (member$e ?v3 )?v2 )(fun_app$e ?v1 ?v3 ))))))):named a26 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_bool_fun$ ))(= (forall ((?v2 A$ ))(=> (fun_app$e (member$f ?v2 )(sup$ ?v0 ))(fun_app$f ?v1 ?v2 )))(forall ((?v2 A_set$ ))(=> (fun_app$d (member$e ?v2 )?v0 )(forall ((?v3 A$ ))(=> (fun_app$e (member$f ?v3 )?v2 )(fun_app$f ?v1 ?v3 ))))))):named a27 ))
(assert (! (forall ((?v0 A_set_set_set$ )(?v1 A_set_set_set_set$ )(?v2 A_set_set$ ))(=> (and (member$b ?v0 ?v1 )(member$a ?v2 ?v0 ))(member$a ?v2 (sup$a ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_llist_set_set$ )(?v1 A_llist_set_set_set$ )(?v2 A_llist_set$ ))(=> (and (member$d ?v0 ?v1 )(member$c ?v2 ?v0 ))(member$c ?v2 (sup$b ?v1 )))):named a29 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set_set$ )(?v2 A_llist$ ))(=> (and (member$c ?v0 ?v1 )(fun_app$a (member$ ?v2 )?v0 ))(fun_app$a (member$ ?v2 )(sup$c ?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_set_set_set$ )(?v2 A_set$ ))(=> (and (member$a ?v0 ?v1 )(fun_app$d (member$e ?v2 )?v0 ))(fun_app$d (member$e ?v2 )(sup$d ?v1 )))):named a31 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_set$ )(?v2 A$ ))(=> (and (fun_app$d (member$e ?v0 )?v1 )(fun_app$e (member$f ?v2 )?v0 ))(fun_app$e (member$f ?v2 )(sup$ ?v1 )))):named a32 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_llist_a_set_fun$ )(?v2 A_llist$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$ ?v1 ?v2 ))(fun_app$a (member$ ?v2 )?v3 ))(fun_app$d (member$e ?v0 )(image$ ?v1 ?v3 )))):named a33 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_fun$ )(?v2 A$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$g ?v1 ?v2 ))(fun_app$e (member$f ?v2 )?v3 ))(fun_app$e (member$f ?v0 )(fun_app$h (image$a ?v1 )?v3 )))):named a34 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist_a_fun$ )(?v2 A_llist$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$i ?v1 ?v2 ))(fun_app$a (member$ ?v2 )?v3 ))(fun_app$e (member$f ?v0 )(image$b ?v1 ?v3 )))):named a35 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_a_llist_fun$ )(?v2 A$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$j ?v1 ?v2 ))(fun_app$e (member$f ?v2 )?v3 ))(fun_app$a (member$ ?v0 )(image$c ?v1 ?v3 )))):named a36 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_a_set_fun$ )(?v2 A$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$k ?v1 ?v2 ))(fun_app$e (member$f ?v2 )?v3 ))(fun_app$d (member$e ?v0 )(image$d ?v1 ?v3 )))):named a37 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set_a_fun$ )(?v2 A_set$ )(?v3 A_set_set$ ))(=> (and (= ?v0 (fun_app$l ?v1 ?v2 ))(fun_app$d (member$e ?v2 )?v3 ))(fun_app$e (member$f ?v0 )(image$e ?v1 ?v3 )))):named a38 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$m ?v1 ?v2 ))(fun_app$a (member$ ?v2 )?v3 ))(fun_app$a (member$ ?v0 )(image$f ?v1 ?v3 )))):named a39 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set_a_llist_fun$ )(?v2 A_set$ )(?v3 A_set_set$ ))(=> (and (= ?v0 (fun_app$n ?v1 ?v2 ))(fun_app$d (member$e ?v2 )?v3 ))(fun_app$a (member$ ?v0 )(image$g ?v1 ?v3 )))):named a40 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_a_set_fun$ )(?v2 A_set$ )(?v3 A_set_set$ ))(=> (and (= ?v0 (fun_app$h ?v1 ?v2 ))(fun_app$d (member$e ?v2 )?v3 ))(fun_app$d (member$e ?v0 )(image$h ?v1 ?v3 )))):named a41 ))
(assert (! (forall ((?v0 A_set_set$ )(?v1 A_a_set_set_fun$ )(?v2 A$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$o ?v1 ?v2 ))(fun_app$e (member$f ?v2 )?v3 ))(member$a ?v0 (image$i ?v1 ?v3 )))):named a42 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set$ )(?v2 A_set_a_set_bool_fun_fun$ )(?v3 A_llist_a_set_fun$ ))(=> (and (fun_app$a (chain$ ?v0 )?v1 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (and (fun_app$a (member$ ?v4 )?v1 )(and (fun_app$a (member$ ?v5 )?v1 )(fun_app$b (fun_app$c ?v0 ?v4 )?v5 )))(fun_app$e (fun_app$p ?v2 (fun_app$ ?v3 ?v4 ))(fun_app$ ?v3 ?v5 )))))(fun_app$d (chain$a ?v2 )(image$ ?v3 ?v1 )))):named a43 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set$ )(?v2 A_llist_a_llist_bool_fun_fun$ )(?v3 A_llist_a_llist_fun$ ))(=> (and (fun_app$a (chain$ ?v0 )?v1 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (and (fun_app$a (member$ ?v4 )?v1 )(and (fun_app$a (member$ ?v5 )?v1 )(fun_app$b (fun_app$c ?v0 ?v4 )?v5 )))(fun_app$b (fun_app$c ?v2 (fun_app$m ?v3 ?v4 ))(fun_app$m ?v3 ?v5 )))))(fun_app$a (chain$ ?v2 )(image$f ?v3 ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_set$ )(?v2 A_llist_a_llist_bool_fun_fun$ )(?v3 A_a_llist_fun$ ))(=> (and (fun_app$e (chain$b ?v0 )?v1 )(forall ((?v4 A$ )(?v5 A$ ))(=> (and (fun_app$e (member$f ?v4 )?v1 )(and (fun_app$e (member$f ?v5 )?v1 )(fun_app$f (fun_app$q ?v0 ?v4 )?v5 )))(fun_app$b (fun_app$c ?v2 (fun_app$j ?v3 ?v4 ))(fun_app$j ?v3 ?v5 )))))(fun_app$a (chain$ ?v2 )(image$c ?v3 ?v1 )))):named a45 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_set$ )(?v2 A_set_a_set_bool_fun_fun$ )(?v3 A_a_set_fun$ ))(=> (and (fun_app$e (chain$b ?v0 )?v1 )(forall ((?v4 A$ )(?v5 A$ ))(=> (and (fun_app$e (member$f ?v4 )?v1 )(and (fun_app$e (member$f ?v5 )?v1 )(fun_app$f (fun_app$q ?v0 ?v4 )?v5 )))(fun_app$e (fun_app$p ?v2 (fun_app$k ?v3 ?v4 ))(fun_app$k ?v3 ?v5 )))))(fun_app$d (chain$a ?v2 )(image$d ?v3 ?v1 )))):named a46 ))
(assert (! (forall ((?v0 A_set_a_set_bool_fun_fun$ )(?v1 A_set_set$ )(?v2 A_llist_a_llist_bool_fun_fun$ )(?v3 A_set_a_llist_fun$ ))(=> (and (fun_app$d (chain$a ?v0 )?v1 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (and (fun_app$d (member$e ?v4 )?v1 )(and (fun_app$d (member$e ?v5 )?v1 )(fun_app$e (fun_app$p ?v0 ?v4 )?v5 )))(fun_app$b (fun_app$c ?v2 (fun_app$n ?v3 ?v4 ))(fun_app$n ?v3 ?v5 )))))(fun_app$a (chain$ ?v2 )(image$g ?v3 ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_set_a_set_bool_fun_fun$ )(?v1 A_set_set$ )(?v2 A_set_a_set_bool_fun_fun$ )(?v3 A_set_a_set_fun$ ))(=> (and (fun_app$d (chain$a ?v0 )?v1 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (and (fun_app$d (member$e ?v4 )?v1 )(and (fun_app$d (member$e ?v5 )?v1 )(fun_app$e (fun_app$p ?v0 ?v4 )?v5 )))(fun_app$e (fun_app$p ?v2 (fun_app$h ?v3 ?v4 ))(fun_app$h ?v3 ?v5 )))))(fun_app$d (chain$a ?v2 )(image$h ?v3 ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_set$ )(?v2 A_a_bool_fun_fun$ )(?v3 A_a_fun$ ))(=> (and (fun_app$e (chain$b ?v0 )?v1 )(forall ((?v4 A$ )(?v5 A$ ))(=> (and (fun_app$e (member$f ?v4 )?v1 )(and (fun_app$e (member$f ?v5 )?v1 )(fun_app$f (fun_app$q ?v0 ?v4 )?v5 )))(fun_app$f (fun_app$q ?v2 (fun_app$g ?v3 ?v4 ))(fun_app$g ?v3 ?v5 )))))(fun_app$e (chain$b ?v2 )(fun_app$h (image$a ?v3 )?v1 )))):named a49 ))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$ )(?v1 A_llist_set$ )(?v2 A_a_bool_fun_fun$ )(?v3 A_llist_a_fun$ ))(=> (and (fun_app$a (chain$ ?v0 )?v1 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (and (fun_app$a (member$ ?v4 )?v1 )(and (fun_app$a (member$ ?v5 )?v1 )(fun_app$b (fun_app$c ?v0 ?v4 )?v5 )))(fun_app$f (fun_app$q ?v2 (fun_app$i ?v3 ?v4 ))(fun_app$i ?v3 ?v5 )))))(fun_app$e (chain$b ?v2 )(image$b ?v3 ?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_set_a_set_bool_fun_fun$ )(?v1 A_set_set$ )(?v2 A_a_bool_fun_fun$ )(?v3 A_set_a_fun$ ))(=> (and (fun_app$d (chain$a ?v0 )?v1 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (and (fun_app$d (member$e ?v4 )?v1 )(and (fun_app$d (member$e ?v5 )?v1 )(fun_app$e (fun_app$p ?v0 ?v4 )?v5 )))(fun_app$f (fun_app$q ?v2 (fun_app$l ?v3 ?v4 ))(fun_app$l ?v3 ?v5 )))))(fun_app$e (chain$b ?v2 )(image$e ?v3 ?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_set_set_a_set_set_bool_fun_fun$ )(?v1 A_set_set_set$ )(?v2 A_a_bool_fun_fun$ )(?v3 A_set_set_a_fun$ ))(=> (and (chain$c ?v0 ?v1 )(forall ((?v4 A_set_set$ )(?v5 A_set_set$ ))(=> (and (member$a ?v4 ?v1 )(and (member$a ?v5 ?v1 )(fun_app$d (fun_app$r ?v0 ?v4 )?v5 )))(fun_app$f (fun_app$q ?v2 (fun_app$s ?v3 ?v4 ))(fun_app$s ?v3 ?v5 )))))(fun_app$e (chain$b ?v2 )(image$j ?v3 ?v1 )))):named a52 ))
(check-sat )
;(get-unsat-core )
