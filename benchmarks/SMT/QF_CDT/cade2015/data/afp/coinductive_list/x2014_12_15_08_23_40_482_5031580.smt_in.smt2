;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort Bool_a_fun$ 0 )
(declare-sort Bool_b_fun$ 0 )
(declare-sort Bool_bool_fun$ 0 )
(declare-sort A_b_prod_a_fun$ 0 )
(declare-sort A_b_prod_b_fun$ 0 )
(declare-sort B_a_b_prod_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort A_b_prod_bool_fun$ 0 )
(declare-sort B_b_fun_b_b_fun_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun$ 0 )
(declare-sort A_a_fun_a_bool_fun_fun$ 0 )
(declare-sort A_b_fun_a_bool_fun_fun$ 0 )
(declare-sort B_a_fun_b_bool_fun_fun$ 0 )
(declare-sort B_b_fun_b_bool_fun_fun$ 0 )
(declare-sort B_bool_fun_b_b_fun_fun$ 0 )
(declare-sort B_bool_fun_b_bool_fun_fun$ 0 )
(declare-sort B_a_b_prod_fun_b_b_fun_fun$ 0 )
(declare-sort Bool_a_fun_bool_bool_fun_fun$ 0 )
(declare-sort Bool_b_fun_bool_bool_fun_fun$ 0 )
(declare-sort B_a_b_prod_fun_b_bool_fun_fun$ 0 )
(declare-sort Bool_bool_fun_bool_bool_fun_fun$ 0 )
(declare-sort A_b_prod_a_fun_a_b_prod_b_fun_fun$ 0 )
(declare-sort A_b_prod_b_fun_a_b_prod_a_fun_fun$ 0 )
(declare-sort A_b_prod_b_fun_a_b_prod_b_fun_fun$ 0 )
(declare-sort A_b_prod_a_fun_a_b_prod_bool_fun_fun$ 0 )
(declare-sort A_b_prod_b_fun_a_b_prod_bool_fun_fun$ 0 )
(declare-sort A_b_prod_bool_fun_a_b_prod_b_fun_fun$ 0 )
(declare-sort A_b_prod_bool_fun_a_b_prod_bool_fun_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun_a_b_prod_b_fun_fun$ 0 )
(declare-sort A_b_prod_a_b_prod_fun_a_b_prod_bool_fun_fun$ 0 )
(declare-datatypes ()((A_b_prod$ (pair$ (fst$ A$ )(snd$ B$ )))))
(declare-sort A_b_prod_llist$ 0)
(declare-sort A_llist$ 0)
(declare-sort B_llist$ 0)
(declare-fun lNil$ ()A_b_prod_llist$)
(declare-fun lhd$ (A_b_prod_llist$)A_b_prod$)
(declare-fun ltl$ (A_b_prod_llist$)A_b_prod_llist$)
(declare-fun lCons$ (A_b_prod$ A_b_prod_llist$ )A_b_prod_llist$)
(declare-fun lNil$a ()A_llist$)
(declare-fun lhd$a (A_llist$)A$)
(declare-fun ltl$a (A_llist$)A_llist$)
(declare-fun lCons$a (A$ A_llist$ )A_llist$)
(declare-fun lNil$b ()B_llist$)
(declare-fun lhd$b (B_llist$)B$)
(declare-fun ltl$b (B_llist$)B_llist$)
(declare-fun lCons$b (B$ B_llist$ )B_llist$)
(declare-fun p$ ()B_bool_fun$ )
(declare-fun uu$ ()A_b_prod_b_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun uua$ ()A_b_prod_a_fun$ )
(declare-fun comp$ (B_bool_fun$ )A_b_prod_b_fun_a_b_prod_bool_fun_fun$ )
(declare-fun lzip$ (A_llist$ B_llist$ )A_b_prod_llist$ )
(declare-fun comp$a (Bool_bool_fun$ )B_bool_fun_b_bool_fun_fun$ )
(declare-fun comp$b (B_bool_fun$ )B_b_fun_b_bool_fun_fun$ )
(declare-fun comp$c (Bool_bool_fun$ )A_b_prod_bool_fun_a_b_prod_bool_fun_fun$ )
(declare-fun comp$d (B_b_fun$ )A_b_prod_b_fun_a_b_prod_b_fun_fun$ )
(declare-fun comp$e (A_bool_fun$ )A_b_prod_a_fun_a_b_prod_bool_fun_fun$ )
(declare-fun comp$f (A_bool_fun$ )Bool_a_fun_bool_bool_fun_fun$ )
(declare-fun comp$g (A_bool_fun$ )B_a_fun_b_bool_fun_fun$ )
(declare-fun comp$h (A_bool_fun$ )A_a_fun_a_bool_fun_fun$ )
(declare-fun comp$i (A_b_fun$ )A_b_prod_a_fun_a_b_prod_b_fun_fun$ )
(declare-fun comp$j (A_b_prod_b_fun$ )A_b_prod_a_b_prod_fun_a_b_prod_b_fun_fun$ )
(declare-fun comp$k (A_b_prod_bool_fun$ )A_b_prod_a_b_prod_fun_a_b_prod_bool_fun_fun$ )
(declare-fun comp$l (Bool_bool_fun$ )Bool_bool_fun_bool_bool_fun_fun$ )
(declare-fun comp$m (Bool_b_fun$ )B_bool_fun_b_b_fun_fun$ )
(declare-fun comp$n (B_bool_fun$ )Bool_b_fun_bool_bool_fun_fun$ )
(declare-fun comp$o (B_b_fun$ )B_b_fun_b_b_fun_fun$ )
(declare-fun comp$p (Bool_b_fun$ )A_b_prod_bool_fun_a_b_prod_b_fun_fun$ )
(declare-fun comp$q (B_bool_fun$ )A_b_fun_a_bool_fun_fun$ )
(declare-fun comp$r (A_b_prod_bool_fun$ )B_a_b_prod_fun_b_bool_fun_fun$ )
(declare-fun comp$s (A_b_prod_b_fun$ )B_a_b_prod_fun_b_b_fun_fun$ )
(declare-fun comp$t (B_a_fun$ )A_b_prod_b_fun_a_b_prod_a_fun_fun$ )
(declare-fun sndsp$ (A_b_prod$ )B_bool_fun$ )
(declare-fun fun_app$ (A_b_prod_b_fun$ A_b_prod$ )B$ )
(declare-fun fun_app$a (A_b_prod_a_fun$ A_b_prod$ )A$ )
(declare-fun fun_app$b (A_b_prod_b_fun_a_b_prod_bool_fun_fun$ A_b_prod_b_fun$ )A_b_prod_bool_fun$ )
(declare-fun fun_app$c (A_b_prod_bool_fun$ A_b_prod$ )Bool )
(declare-fun fun_app$d (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$e (B_bool_fun_b_bool_fun_fun$ B_bool_fun$ )B_bool_fun$ )
(declare-fun fun_app$f (Bool_bool_fun$ Bool )Bool )
(declare-fun fun_app$g (B_b_fun_b_bool_fun_fun$ B_b_fun$ )B_bool_fun$ )
(declare-fun fun_app$h (B_b_fun$ B$ )B$ )
(declare-fun fun_app$i (A_b_prod_bool_fun_a_b_prod_bool_fun_fun$ A_b_prod_bool_fun$ )A_b_prod_bool_fun$ )
(declare-fun fun_app$j (A_b_prod_b_fun_a_b_prod_b_fun_fun$ A_b_prod_b_fun$ )A_b_prod_b_fun$ )
(declare-fun fun_app$k (A_b_prod_a_fun_a_b_prod_bool_fun_fun$ A_b_prod_a_fun$ )A_b_prod_bool_fun$ )
(declare-fun fun_app$l (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$m (Bool_a_fun_bool_bool_fun_fun$ Bool_a_fun$ )Bool_bool_fun$ )
(declare-fun fun_app$n (Bool_a_fun$ Bool )A$ )
(declare-fun fun_app$o (B_a_fun_b_bool_fun_fun$ B_a_fun$ )B_bool_fun$ )
(declare-fun fun_app$p (B_a_fun$ B$ )A$ )
(declare-fun fun_app$q (A_a_fun_a_bool_fun_fun$ A_a_fun$ )A_bool_fun$ )
(declare-fun fun_app$r (A_a_fun$ A$ )A$ )
(declare-fun fun_app$s (A_b_prod_a_fun_a_b_prod_b_fun_fun$ A_b_prod_a_fun$ )A_b_prod_b_fun$ )
(declare-fun fun_app$t (A_b_fun$ A$ )B$ )
(declare-fun fun_app$u (A_b_prod_a_b_prod_fun_a_b_prod_b_fun_fun$ A_b_prod_a_b_prod_fun$ )A_b_prod_b_fun$ )
(declare-fun fun_app$v (A_b_prod_a_b_prod_fun_a_b_prod_bool_fun_fun$ A_b_prod_a_b_prod_fun$ )A_b_prod_bool_fun$ )
(declare-fun fun_app$w (Bool_bool_fun_bool_bool_fun_fun$ Bool_bool_fun$ )Bool_bool_fun$ )
(declare-fun fun_app$x (B_bool_fun_b_b_fun_fun$ B_bool_fun$ )B_b_fun$ )
(declare-fun fun_app$y (Bool_b_fun_bool_bool_fun_fun$ Bool_b_fun$ )Bool_bool_fun$ )
(declare-fun fun_app$z (B_b_fun_b_b_fun_fun$ B_b_fun$ )B_b_fun$ )
(declare-fun fun_app$aa (A_b_prod_bool_fun_a_b_prod_b_fun_fun$ A_b_prod_bool_fun$ )A_b_prod_b_fun$ )
(declare-fun fun_app$ab (A_b_fun_a_bool_fun_fun$ A_b_fun$ )A_bool_fun$ )
(declare-fun fun_app$ac (B_a_b_prod_fun_b_bool_fun_fun$ B_a_b_prod_fun$ )B_bool_fun$ )
(declare-fun fun_app$ad (B_a_b_prod_fun_b_b_fun_fun$ B_a_b_prod_fun$ )B_b_fun$ )
(declare-fun fun_app$ae (A_b_prod_b_fun_a_b_prod_a_fun_fun$ A_b_prod_b_fun$ )A_b_prod_a_fun$ )
(declare-fun fun_app$af (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun ltakeWhile$ (B_bool_fun$ B_llist$ )B_llist$ )
(declare-fun ltakeWhile$a (A_b_prod_bool_fun$ A_b_prod_llist$ )A_b_prod_llist$ )
(declare-fun ltakeWhile$b (A_bool_fun$ A_llist$ )A_llist$ )
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$ uu$ ?v0 )(snd$ ?v0 )):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_b_prod$ ))(! (= (fun_app$a uua$ ?v0 )(fst$ ?v0 )):pattern ((fun_app$a uua$ ?v0 )))):named a1 ))
(assert (! (not (= (lzip$ xs$ (ltakeWhile$ p$ ys$ ))(ltakeWhile$a (fun_app$b (comp$ p$ )uu$ )(lzip$ xs$ ys$ )))):named a2 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$b (comp$ ?v0 )?v1 )?v2 )(fun_app$d ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$b (comp$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$e (comp$a ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$d ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$e (comp$a ?v0 )?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$g (comp$b ?v0 )?v1 )?v2 )(fun_app$d ?v0 (fun_app$h ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$g (comp$b ?v0 )?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$i (comp$c ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$c ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$i (comp$c ?v0 )?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$ (fun_app$j (comp$d ?v0 )?v1 )?v2 )(fun_app$h ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$j (comp$d ?v0 )?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$k (comp$e ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$a ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$k (comp$e ?v0 )?v1 )?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 Bool_a_fun$ )(?v2 Bool ))(! (= (fun_app$f (fun_app$m (comp$f ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$n ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$m (comp$f ?v0 )?v1 )?v2 )))):named a9 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_a_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$o (comp$g ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$p ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$o (comp$g ?v0 )?v1 )?v2 )))):named a10 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_a_fun$ )(?v2 A$ ))(! (= (fun_app$l (fun_app$q (comp$h ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$r ?v1 ?v2 ))):pattern ((fun_app$l (fun_app$q (comp$h ?v0 )?v1 )?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$ (fun_app$s (comp$i ?v0 )?v1 )?v2 )(fun_app$t ?v0 (fun_app$a ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$s (comp$i ?v0 )?v1 )?v2 )))):named a12 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(= (lzip$ (ltakeWhile$b ?v0 ?v1 )?v2 )(ltakeWhile$a (fun_app$k (comp$e ?v0 )uua$ )(lzip$ ?v1 ?v2 )))):named a13 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$i (comp$c ?v0 )(fun_app$b (comp$ ?v1 )?v2 ))(fun_app$b (comp$ (fun_app$e (comp$a ?v0 )?v1 ))?v2 ))):named a14 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$b (comp$ ?v0 )(fun_app$j (comp$d ?v1 )?v2 ))(fun_app$b (comp$ (fun_app$g (comp$b ?v0 )?v1 ))?v2 ))):named a15 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_a_b_prod_fun$ ))(= (fun_app$b (comp$ ?v0 )(fun_app$u (comp$j ?v1 )?v2 ))(fun_app$v (comp$k (fun_app$b (comp$ ?v0 )?v1 ))?v2 ))):named a16 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 Bool_bool_fun$ )(?v2 B_bool_fun$ ))(= (fun_app$e (comp$a ?v0 )(fun_app$e (comp$a ?v1 )?v2 ))(fun_app$e (comp$a (fun_app$w (comp$l ?v0 )?v1 ))?v2 ))):named a17 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_b_fun$ ))(= (fun_app$e (comp$a ?v0 )(fun_app$g (comp$b ?v1 )?v2 ))(fun_app$g (comp$b (fun_app$e (comp$a ?v0 )?v1 ))?v2 ))):named a18 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 B_bool_fun$ ))(= (fun_app$g (comp$b ?v0 )(fun_app$x (comp$m ?v1 )?v2 ))(fun_app$e (comp$a (fun_app$y (comp$n ?v0 )?v1 ))?v2 ))):named a19 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ ))(= (fun_app$g (comp$b ?v0 )(fun_app$z (comp$o ?v1 )?v2 ))(fun_app$g (comp$b (fun_app$g (comp$b ?v0 )?v1 ))?v2 ))):named a20 ))
(assert (! (forall ((?v0 Bool_b_fun$ )(?v1 B_bool_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$aa (comp$p ?v0 )(fun_app$b (comp$ ?v1 )?v2 ))(fun_app$j (comp$d (fun_app$x (comp$m ?v0 )?v1 ))?v2 ))):named a21 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 A_b_prod_bool_fun$ ))(= (fun_app$b (comp$ ?v0 )(fun_app$aa (comp$p ?v1 )?v2 ))(fun_app$i (comp$c (fun_app$y (comp$n ?v0 )?v1 ))?v2 ))):named a22 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_fun$ )(?v2 A_b_prod_a_fun$ ))(= (fun_app$b (comp$ ?v0 )(fun_app$s (comp$i ?v1 )?v2 ))(fun_app$k (comp$e (fun_app$ab (comp$q ?v0 )?v1 ))?v2 ))):named a23 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$b (comp$ (fun_app$e (comp$a ?v0 )?v1 ))?v2 )(fun_app$i (comp$c ?v0 )(fun_app$b (comp$ ?v1 )?v2 )))):named a24 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$b (comp$ (fun_app$g (comp$b ?v0 )?v1 ))?v2 )(fun_app$b (comp$ ?v0 )(fun_app$j (comp$d ?v1 )?v2 )))):named a25 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_a_b_prod_fun$ ))(= (fun_app$v (comp$k (fun_app$b (comp$ ?v0 )?v1 ))?v2 )(fun_app$b (comp$ ?v0 )(fun_app$u (comp$j ?v1 )?v2 )))):named a26 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 Bool_bool_fun$ )(?v2 B_bool_fun$ ))(= (fun_app$e (comp$a (fun_app$w (comp$l ?v0 )?v1 ))?v2 )(fun_app$e (comp$a ?v0 )(fun_app$e (comp$a ?v1 )?v2 )))):named a27 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 B_bool_fun$ ))(= (fun_app$e (comp$a (fun_app$y (comp$n ?v0 )?v1 ))?v2 )(fun_app$g (comp$b ?v0 )(fun_app$x (comp$m ?v1 )?v2 )))):named a28 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_b_fun$ ))(= (fun_app$g (comp$b (fun_app$e (comp$a ?v0 )?v1 ))?v2 )(fun_app$e (comp$a ?v0 )(fun_app$g (comp$b ?v1 )?v2 )))):named a29 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ ))(= (fun_app$g (comp$b (fun_app$g (comp$b ?v0 )?v1 ))?v2 )(fun_app$g (comp$b ?v0 )(fun_app$z (comp$o ?v1 )?v2 )))):named a30 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 B_a_b_prod_fun$ ))(= (fun_app$ac (comp$r (fun_app$b (comp$ ?v0 )?v1 ))?v2 )(fun_app$g (comp$b ?v0 )(fun_app$ad (comp$s ?v1 )?v2 )))):named a31 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 B_a_b_prod_fun$ ))(= (fun_app$ac (comp$r (fun_app$i (comp$c ?v0 )?v1 ))?v2 )(fun_app$e (comp$a ?v0 )(fun_app$ac (comp$r ?v1 )?v2 )))):named a32 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_a_fun$ )(?v2 A_b_prod_b_fun$ ))(= (fun_app$b (comp$ (fun_app$o (comp$g ?v0 )?v1 ))?v2 )(fun_app$k (comp$e ?v0 )(fun_app$ae (comp$t ?v1 )?v2 )))):named a33 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$b (comp$ ?v0 )?v1 )?v2 )(fun_app$d ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$b (comp$ ?v0 )?v1 )?v2 )))):named a34 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$e (comp$a ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$d ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$e (comp$a ?v0 )?v1 )?v2 )))):named a35 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$g (comp$b ?v0 )?v1 )?v2 )(fun_app$d ?v0 (fun_app$h ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$g (comp$b ?v0 )?v1 )?v2 )))):named a36 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$i (comp$c ?v0 )?v1 )?v2 )(fun_app$f ?v0 (fun_app$c ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$i (comp$c ?v0 )?v1 )?v2 )))):named a37 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$ (fun_app$j (comp$d ?v0 )?v1 )?v2 )(fun_app$h ?v0 (fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$j (comp$d ?v0 )?v1 )?v2 )))):named a38 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$c (fun_app$k (comp$e ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$a ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$k (comp$e ?v0 )?v1 )?v2 )))):named a39 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 Bool_a_fun$ )(?v2 Bool ))(! (= (fun_app$f (fun_app$m (comp$f ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$n ?v1 ?v2 ))):pattern ((fun_app$f (fun_app$m (comp$f ?v0 )?v1 )?v2 )))):named a40 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_a_fun$ )(?v2 B$ ))(! (= (fun_app$d (fun_app$o (comp$g ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$p ?v1 ?v2 ))):pattern ((fun_app$d (fun_app$o (comp$g ?v0 )?v1 )?v2 )))):named a41 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_a_fun$ )(?v2 A$ ))(! (= (fun_app$l (fun_app$q (comp$h ?v0 )?v1 )?v2 )(fun_app$l ?v0 (fun_app$r ?v1 ?v2 ))):pattern ((fun_app$l (fun_app$q (comp$h ?v0 )?v1 )?v2 )))):named a42 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod$ ))(! (= (fun_app$ (fun_app$s (comp$i ?v0 )?v1 )?v2 )(fun_app$t ?v0 (fun_app$a ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$s (comp$i ?v0 )?v1 )?v2 )))):named a43 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ ))(=> (and (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$ ?v3 ?v4 ))))false ))false )):named a44 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(=> (forall ((?v4 B$ ))(= (fun_app$f ?v0 (fun_app$d ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$d ?v3 ?v4 ))))false ))false )):named a45 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(=> (forall ((?v4 B$ ))(= (fun_app$f ?v0 (fun_app$d ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$h ?v3 ?v4 ))))false ))false )):named a46 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(=> (forall ((?v4 B$ ))(= (fun_app$d ?v0 (fun_app$h ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$d ?v3 ?v4 ))))false ))false )):named a47 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(=> (forall ((?v4 B$ ))(= (fun_app$d ?v0 (fun_app$h ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$h ?v3 ?v4 ))))false ))false )):named a48 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 A_b_prod_bool_fun$ ))(=> (and (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$i (comp$c ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$c ?v3 ?v4 ))))false ))false )):named a49 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_bool_fun$ )(?v3 A_b_prod_a_fun$ ))(=> (and (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$k (comp$e ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$l ?v2 (fun_app$a ?v3 ?v4 ))))false ))false )):named a50 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ ))(=> (and (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$ ?v3 ?v4 ))))false ))false )):named a51 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 A_b_prod_bool_fun$ ))(=> (and (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$i (comp$c ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$c ?v3 ?v4 ))))false ))false )):named a52 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 A_bool_fun$ )(?v3 A_b_prod_a_fun$ ))(=> (and (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$k (comp$e ?v2 )?v3 ))(=> (forall ((?v4 A_b_prod$ ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$l ?v2 (fun_app$a ?v3 ?v4 ))))false ))false )):named a53 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ )(?v4 Bool_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(= (fun_app$e (comp$a ?v4 )?v2 )?v5 ))(= (fun_app$b (comp$ (fun_app$e (comp$a ?v4 )?v0 ))?v1 )(fun_app$b (comp$ ?v5 )?v3 )))):named a54 ))
(assert (! (forall ((?v0 A_b_prod_b_fun$ )(?v1 A_b_prod_a_b_prod_fun$ )(?v2 B_b_fun$ )(?v3 A_b_prod_b_fun$ )(?v4 B_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$u (comp$j ?v0 )?v1 )(fun_app$j (comp$d ?v2 )?v3 ))(= (fun_app$g (comp$b ?v4 )?v2 )?v5 ))(= (fun_app$v (comp$k (fun_app$b (comp$ ?v4 )?v0 ))?v1 )(fun_app$b (comp$ ?v5 )?v3 )))):named a55 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_b_fun$ )(?v3 A_b_prod_a_b_prod_fun$ )(?v4 B_bool_fun$ )(?v5 A_b_prod_bool_fun$ ))(=> (and (= (fun_app$j (comp$d ?v0 )?v1 )(fun_app$u (comp$j ?v2 )?v3 ))(= (fun_app$b (comp$ ?v4 )?v2 )?v5 ))(= (fun_app$b (comp$ (fun_app$g (comp$b ?v4 )?v0 ))?v1 )(fun_app$v (comp$k ?v5 )?v3 )))):named a56 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun$ )(?v2 Bool_b_fun$ )(?v3 B_bool_fun$ )(?v4 B_bool_fun$ )(?v5 Bool_bool_fun$ ))(=> (and (= (fun_app$z (comp$o ?v0 )?v1 )(fun_app$x (comp$m ?v2 )?v3 ))(= (fun_app$y (comp$n ?v4 )?v2 )?v5 ))(= (fun_app$g (comp$b (fun_app$g (comp$b ?v4 )?v0 ))?v1 )(fun_app$e (comp$a ?v5 )?v3 )))):named a57 ))
(assert (! (forall ((?v0 Bool_b_fun$ )(?v1 B_bool_fun$ )(?v2 B_b_fun$ )(?v3 B_b_fun$ )(?v4 B_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$x (comp$m ?v0 )?v1 )(fun_app$z (comp$o ?v2 )?v3 ))(= (fun_app$g (comp$b ?v4 )?v2 )?v5 ))(= (fun_app$e (comp$a (fun_app$y (comp$n ?v4 )?v0 ))?v1 )(fun_app$g (comp$b ?v5 )?v3 )))):named a58 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ )(?v3 B_b_fun$ )(?v4 B_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$z (comp$o ?v0 )?v1 )(fun_app$z (comp$o ?v2 )?v3 ))(= (fun_app$g (comp$b ?v4 )?v2 )?v5 ))(= (fun_app$g (comp$b (fun_app$g (comp$b ?v4 )?v0 ))?v1 )(fun_app$g (comp$b ?v5 )?v3 )))):named a59 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 Bool_bool_fun$ )(?v5 Bool_bool_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$w (comp$l ?v4 )?v2 )?v5 ))(= (fun_app$e (comp$a (fun_app$w (comp$l ?v4 )?v0 ))?v1 )(fun_app$e (comp$a ?v5 )?v3 )))):named a60 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 Bool_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$e (comp$a ?v4 )?v2 )?v5 ))(= (fun_app$e (comp$a (fun_app$w (comp$l ?v4 )?v0 ))?v1 )(fun_app$g (comp$b ?v5 )?v3 )))):named a61 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 Bool_bool_fun$ )(?v5 Bool_bool_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$w (comp$l ?v4 )?v2 )?v5 ))(= (fun_app$g (comp$b (fun_app$e (comp$a ?v4 )?v0 ))?v1 )(fun_app$e (comp$a ?v5 )?v3 )))):named a62 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 Bool_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$e (comp$a ?v4 )?v2 )?v5 ))(= (fun_app$g (comp$b (fun_app$e (comp$a ?v4 )?v0 ))?v1 )(fun_app$g (comp$b ?v5 )?v3 )))):named a63 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 A_b_prod_b_fun$ )(?v5 A_b_prod_b_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$j (comp$d ?v3 )?v4 )?v5 ))(= (fun_app$i (comp$c ?v0 )(fun_app$b (comp$ ?v1 )?v4 ))(fun_app$b (comp$ ?v2 )?v5 )))):named a64 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 A_b_prod_b_fun$ )(?v5 A_b_prod_bool_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$b (comp$ ?v3 )?v4 )?v5 ))(= (fun_app$b (comp$ ?v0 )(fun_app$j (comp$d ?v1 )?v4 ))(fun_app$i (comp$c ?v2 )?v5 )))):named a65 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ )(?v4 A_b_prod_a_b_prod_fun$ )(?v5 A_b_prod_b_fun$ ))(=> (and (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(= (fun_app$u (comp$j ?v3 )?v4 )?v5 ))(= (fun_app$b (comp$ ?v0 )(fun_app$u (comp$j ?v1 )?v4 ))(fun_app$b (comp$ ?v2 )?v5 )))):named a66 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 Bool_bool_fun$ )(?v2 B_bool_fun$ )(?v3 Bool_b_fun$ )(?v4 B_bool_fun$ )(?v5 B_b_fun$ ))(=> (and (= (fun_app$w (comp$l ?v0 )?v1 )(fun_app$y (comp$n ?v2 )?v3 ))(= (fun_app$x (comp$m ?v3 )?v4 )?v5 ))(= (fun_app$e (comp$a ?v0 )(fun_app$e (comp$a ?v1 )?v4 ))(fun_app$g (comp$b ?v2 )?v5 )))):named a67 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 Bool_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 Bool_bool_fun$ )(?v4 B_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$w (comp$l ?v0 )?v1 )(fun_app$w (comp$l ?v2 )?v3 ))(= (fun_app$e (comp$a ?v3 )?v4 )?v5 ))(= (fun_app$e (comp$a ?v0 )(fun_app$e (comp$a ?v1 )?v4 ))(fun_app$e (comp$a ?v2 )?v5 )))):named a68 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 Bool_bool_fun$ )(?v4 B_bool_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$y (comp$n ?v0 )?v1 )(fun_app$w (comp$l ?v2 )?v3 ))(= (fun_app$e (comp$a ?v3 )?v4 )?v5 ))(= (fun_app$g (comp$b ?v0 )(fun_app$x (comp$m ?v1 )?v4 ))(fun_app$e (comp$a ?v2 )?v5 )))):named a69 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 B_b_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$g (comp$b ?v3 )?v4 )?v5 ))(= (fun_app$e (comp$a ?v0 )(fun_app$g (comp$b ?v1 )?v4 ))(fun_app$e (comp$a ?v2 )?v5 )))):named a70 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 B_b_fun$ )(?v5 B_b_fun$ ))(=> (and (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$z (comp$o ?v3 )?v4 )?v5 ))(= (fun_app$e (comp$a ?v0 )(fun_app$g (comp$b ?v1 )?v4 ))(fun_app$g (comp$b ?v2 )?v5 )))):named a71 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 B_b_fun$ )(?v5 B_bool_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$g (comp$b ?v3 )?v4 )?v5 ))(= (fun_app$g (comp$b ?v0 )(fun_app$z (comp$o ?v1 )?v4 ))(fun_app$e (comp$a ?v2 )?v5 )))):named a72 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 B_b_fun$ )(?v5 B_b_fun$ ))(=> (and (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$z (comp$o ?v3 )?v4 )?v5 ))(= (fun_app$g (comp$b ?v0 )(fun_app$z (comp$o ?v1 )?v4 ))(fun_app$g (comp$b ?v2 )?v5 )))):named a73 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$ ?v3 ?v4 ))))):named a74 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 B$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$f ?v0 (fun_app$d ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$d ?v3 ?v4 ))))):named a75 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 B$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$f ?v0 (fun_app$d ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$h ?v3 ?v4 ))))):named a76 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ )(?v4 B$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$e (comp$a ?v2 )?v3 ))(= (fun_app$d ?v0 (fun_app$h ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$d ?v3 ?v4 ))))):named a77 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ )(?v4 B$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )(fun_app$g (comp$b ?v2 )?v3 ))(= (fun_app$d ?v0 (fun_app$h ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$h ?v3 ?v4 ))))):named a78 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 A_b_prod_bool_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$i (comp$c ?v2 )?v3 ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$c ?v3 ?v4 ))))):named a79 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_bool_fun$ )(?v3 A_b_prod_a_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )(fun_app$k (comp$e ?v2 )?v3 ))(= (fun_app$d ?v0 (fun_app$ ?v1 ?v4 ))(fun_app$l ?v2 (fun_app$a ?v3 ?v4 ))))):named a80 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$b (comp$ ?v2 )?v3 ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$d ?v2 (fun_app$ ?v3 ?v4 ))))):named a81 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 A_b_prod_bool_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$i (comp$c ?v2 )?v3 ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$f ?v2 (fun_app$c ?v3 ?v4 ))))):named a82 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 A_bool_fun$ )(?v3 A_b_prod_a_fun$ )(?v4 A_b_prod$ ))(=> (= (fun_app$i (comp$c ?v0 )?v1 )(fun_app$k (comp$e ?v2 )?v3 ))(= (fun_app$f ?v0 (fun_app$c ?v1 ?v4 ))(fun_app$l ?v2 (fun_app$a ?v3 ?v4 ))))):named a83 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_b_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$j (comp$d ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ (fun_app$g (comp$b ?v3 )?v0 ))?v1 )(fun_app$b (comp$ ?v3 )?v2 )))):named a84 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_bool_fun$ )(?v3 Bool_bool_fun$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ (fun_app$e (comp$a ?v3 )?v0 ))?v1 )(fun_app$i (comp$c ?v3 )?v2 )))):named a85 ))
(assert (! (forall ((?v0 A_b_prod_b_fun$ )(?v1 A_b_prod_a_b_prod_fun$ )(?v2 A_b_prod_b_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$u (comp$j ?v0 )?v1 )?v2 )(= (fun_app$v (comp$k (fun_app$b (comp$ ?v3 )?v0 ))?v1 )(fun_app$b (comp$ ?v3 )?v2 )))):named a86 ))
(assert (! (forall ((?v0 Bool_b_fun$ )(?v1 B_bool_fun$ )(?v2 B_b_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$x (comp$m ?v0 )?v1 )?v2 )(= (fun_app$e (comp$a (fun_app$y (comp$n ?v3 )?v0 ))?v1 )(fun_app$g (comp$b ?v3 )?v2 )))):named a87 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$z (comp$o ?v0 )?v1 )?v2 )(= (fun_app$g (comp$b (fun_app$g (comp$b ?v3 )?v0 ))?v1 )(fun_app$g (comp$b ?v3 )?v2 )))):named a88 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 Bool_bool_fun$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )?v2 )(= (fun_app$e (comp$a (fun_app$w (comp$l ?v3 )?v0 ))?v1 )(fun_app$e (comp$a ?v3 )?v2 )))):named a89 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 Bool_bool_fun$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )?v2 )(= (fun_app$g (comp$b (fun_app$e (comp$a ?v3 )?v0 ))?v1 )(fun_app$e (comp$a ?v3 )?v2 )))):named a90 ))
(assert (! (forall ((?v0 A_b_prod_b_fun$ )(?v1 B_a_b_prod_fun$ )(?v2 B_b_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$ad (comp$s ?v0 )?v1 )?v2 )(= (fun_app$ac (comp$r (fun_app$b (comp$ ?v3 )?v0 ))?v1 )(fun_app$g (comp$b ?v3 )?v2 )))):named a91 ))
(assert (! (forall ((?v0 A_b_prod_bool_fun$ )(?v1 B_a_b_prod_fun$ )(?v2 B_bool_fun$ )(?v3 Bool_bool_fun$ ))(=> (= (fun_app$ac (comp$r ?v0 )?v1 )?v2 )(= (fun_app$ac (comp$r (fun_app$i (comp$c ?v3 )?v0 ))?v1 )(fun_app$e (comp$a ?v3 )?v2 )))):named a92 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_a_fun$ )(?v3 A_bool_fun$ ))(=> (= (fun_app$ae (comp$t ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ (fun_app$o (comp$g ?v3 )?v0 ))?v1 )(fun_app$k (comp$e ?v3 )?v2 )))):named a93 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )?v2 )(= (fun_app$i (comp$c ?v0 )(fun_app$b (comp$ ?v1 )?v3 ))(fun_app$b (comp$ ?v2 )?v3 )))):named a94 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 A_b_prod_b_fun$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ ?v0 )(fun_app$j (comp$d ?v1 )?v3 ))(fun_app$b (comp$ ?v2 )?v3 )))):named a95 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_bool_fun$ )(?v3 A_b_prod_a_b_prod_fun$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ ?v0 )(fun_app$u (comp$j ?v1 )?v3 ))(fun_app$v (comp$k ?v2 )?v3 )))):named a96 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 Bool_bool_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$w (comp$l ?v0 )?v1 )?v2 )(= (fun_app$e (comp$a ?v0 )(fun_app$e (comp$a ?v1 )?v3 ))(fun_app$e (comp$a ?v2 )?v3 )))):named a97 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 B_bool_fun$ ))(=> (= (fun_app$y (comp$n ?v0 )?v1 )?v2 )(= (fun_app$g (comp$b ?v0 )(fun_app$x (comp$m ?v1 )?v3 ))(fun_app$e (comp$a ?v2 )?v3 )))):named a98 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )?v2 )(= (fun_app$e (comp$a ?v0 )(fun_app$g (comp$b ?v1 )?v3 ))(fun_app$g (comp$b ?v2 )?v3 )))):named a99 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B_b_fun$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )?v2 )(= (fun_app$g (comp$b ?v0 )(fun_app$z (comp$o ?v1 )?v3 ))(fun_app$g (comp$b ?v2 )?v3 )))):named a100 ))
(assert (! (forall ((?v0 Bool_b_fun$ )(?v1 B_bool_fun$ )(?v2 B_b_fun$ )(?v3 A_b_prod_b_fun$ ))(=> (= (fun_app$x (comp$m ?v0 )?v1 )?v2 )(= (fun_app$aa (comp$p ?v0 )(fun_app$b (comp$ ?v1 )?v3 ))(fun_app$j (comp$d ?v2 )?v3 )))):named a101 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 Bool_b_fun$ )(?v2 Bool_bool_fun$ )(?v3 A_b_prod_bool_fun$ ))(=> (= (fun_app$y (comp$n ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ ?v0 )(fun_app$aa (comp$p ?v1 )?v3 ))(fun_app$i (comp$c ?v2 )?v3 )))):named a102 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_fun$ )(?v2 A_bool_fun$ )(?v3 A_b_prod_a_fun$ ))(=> (= (fun_app$ab (comp$q ?v0 )?v1 )?v2 )(= (fun_app$b (comp$ ?v0 )(fun_app$s (comp$i ?v1 )?v3 ))(fun_app$k (comp$e ?v2 )?v3 )))):named a103 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_bool_fun$ )(?v3 A_b_prod$ ))(=> (= (fun_app$b (comp$ ?v0 )?v1 )?v2 )(= (fun_app$d ?v0 (fun_app$ ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))):named a104 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 B_bool_fun$ )(?v2 B_bool_fun$ )(?v3 B$ ))(=> (= (fun_app$e (comp$a ?v0 )?v1 )?v2 )(= (fun_app$f ?v0 (fun_app$d ?v1 ?v3 ))(fun_app$d ?v2 ?v3 )))):named a105 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_b_fun$ )(?v2 B_bool_fun$ )(?v3 B$ ))(=> (= (fun_app$g (comp$b ?v0 )?v1 )?v2 )(= (fun_app$d ?v0 (fun_app$h ?v1 ?v3 ))(fun_app$d ?v2 ?v3 )))):named a106 ))
(assert (! (forall ((?v0 Bool_bool_fun$ )(?v1 A_b_prod_bool_fun$ )(?v2 A_b_prod_bool_fun$ )(?v3 A_b_prod$ ))(=> (= (fun_app$i (comp$c ?v0 )?v1 )?v2 )(= (fun_app$f ?v0 (fun_app$c ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))):named a107 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_b_prod_b_fun$ )(?v2 A_b_prod_b_fun$ )(?v3 A_b_prod$ ))(=> (= (fun_app$j (comp$d ?v0 )?v1 )?v2 )(= (fun_app$h ?v0 (fun_app$ ?v1 ?v3 ))(fun_app$ ?v2 ?v3 )))):named a108 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod_bool_fun$ )(?v3 A_b_prod$ ))(=> (= (fun_app$k (comp$e ?v0 )?v1 )?v2 )(= (fun_app$l ?v0 (fun_app$a ?v1 ?v3 ))(fun_app$c ?v2 ?v3 )))):named a109 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 Bool_a_fun$ )(?v2 Bool_bool_fun$ )(?v3 Bool ))(=> (= (fun_app$m (comp$f ?v0 )?v1 )?v2 )(= (fun_app$l ?v0 (fun_app$n ?v1 ?v3 ))(fun_app$f ?v2 ?v3 )))):named a110 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 B_a_fun$ )(?v2 B_bool_fun$ )(?v3 B$ ))(=> (= (fun_app$o (comp$g ?v0 )?v1 )?v2 )(= (fun_app$l ?v0 (fun_app$p ?v1 ?v3 ))(fun_app$d ?v2 ?v3 )))):named a111 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_a_fun$ )(?v2 A_bool_fun$ )(?v3 A$ ))(=> (= (fun_app$q (comp$h ?v0 )?v1 )?v2 )(= (fun_app$l ?v0 (fun_app$r ?v1 ?v3 ))(fun_app$l ?v2 ?v3 )))):named a112 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_prod_a_fun$ )(?v2 A_b_prod_b_fun$ )(?v3 A_b_prod$ ))(=> (= (fun_app$s (comp$i ?v0 )?v1 )?v2 )(= (fun_app$t ?v0 (fun_app$a ?v1 ?v3 ))(fun_app$ ?v2 ?v3 )))):named a113 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 A_b_prod$ ))(=> (and (fun_app$l (fun_app$af ?v0 (snd$ ?v1 ))(fst$ ?v1 ))(forall ((?v2 A$ )(?v3 B$ ))(=> (fun_app$l (fun_app$af ?v0 ?v3 )?v2 )false )))false )):named a114 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod$ ))(=> (and (= (fst$ ?v0 )(fst$ ?v1 ))(= (snd$ ?v0 )(snd$ ?v1 )))(= ?v0 ?v1 ))):named a115 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod$ ))(=> (and (= (fst$ ?v0 )(fst$ ?v1 ))(= (snd$ ?v0 )(snd$ ?v1 )))(= ?v0 ?v1 ))):named a116 ))
(assert (! (forall ((?v0 A_b_prod$ )(?v1 A_b_prod$ ))(= (= ?v0 ?v1 )(and (= (fst$ ?v0 )(fst$ ?v1 ))(= (snd$ ?v0 )(snd$ ?v1 ))))):named a117 ))
(assert (! (forall ((?v0 A_b_prod$ ))(fun_app$d (sndsp$ ?v0 )(snd$ ?v0 ))):named a118 ))
(check-sat )
;(get-unsat-core )
