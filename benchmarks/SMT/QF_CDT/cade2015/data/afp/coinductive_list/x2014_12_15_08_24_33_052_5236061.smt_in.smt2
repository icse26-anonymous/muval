;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort B_llist_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_llist_b_llist_bool_fun_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-sort B_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun lNil$a ()B_llist$)
(declare-fun lhd$a (B_llist$)B$)
(declare-fun ltl$a (B_llist$)B_llist$)
(declare-fun lCons$a (B$ B_llist$ )B_llist$)
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun uu$ ()B_b_bool_fun_fun$ )
(declare-fun xs$ ()A_llist$ )
(declare-fun ys$ ()B_llist$ )
(declare-fun uua$ ()B_llist_b_llist_bool_fun_fun$ )
(declare-fun uub$ ()A_a_bool_fun_fun$ )
(declare-fun uuc$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun thesis$ ()Bool )
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$ )Bool )
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$ )B_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$f (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$h (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$i (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$ )B_llist_bool_fun$ )
(declare-fun llist_all2$a (A_a_bool_fun_fun$ )A_llist_a_llist_bool_fun_fun$ )
(declare-fun llist_all2$b (B_a_bool_fun_fun$ B_llist$ )A_llist_bool_fun$ )
(declare-fun llist_all2$c (B_b_bool_fun_fun$ )B_llist_b_llist_bool_fun_fun$ )
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(! (= (fun_app$ (fun_app$a uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$b (fun_app$c uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uuc$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$d (fun_app$e uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uu$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$f (fun_app$g uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (fun_app$g uub$ ?v0 )?v1 )))):named a3 ))
(assert (! (not thesis$ ):named a4 ))
(assert (! (=> (and (= xs$ lNil$ )(= ys$ lNil$a ))thesis$ ):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 B$ )(?v3 B_llist$ ))(=> (and (= xs$ (lCons$ ?v0 ?v1 ))(and (= ys$ (lCons$a ?v2 ?v3 ))(and (fun_app$d (fun_app$h p$ ?v0 )?v2 )(fun_app$ (llist_all2$ p$ ?v1 )?v3 ))))thesis$ )):named a6 ))
(assert (! (fun_app$ (llist_all2$ p$ xs$ )ys$ ):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a8 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a9 ))
(assert (! (=> (and (= xs$ lNil$ )(= ys$ lNil$a ))thesis$ ):named a10 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 A$ )(?v4 A_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$a ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))(and (fun_app$f (fun_app$g ?v0 ?v1 )?v3 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v2 )?v4 ))):pattern ((fun_app$b (fun_app$c (llist_all2$a ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))))):named a11 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ )(?v3 A$ )(?v4 A_llist$ ))(! (= (fun_app$b (llist_all2$b ?v0 (lCons$a ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))(and (fun_app$f (fun_app$i ?v0 ?v1 )?v3 )(fun_app$b (llist_all2$b ?v0 ?v2 )?v4 ))):pattern ((fun_app$b (llist_all2$b ?v0 (lCons$a ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))))):named a12 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ )(?v3 B$ )(?v4 B_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$c ?v0 )(lCons$a ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))(and (fun_app$d (fun_app$e ?v0 ?v1 )?v3 )(fun_app$ (fun_app$a (llist_all2$c ?v0 )?v2 )?v4 ))):pattern ((fun_app$ (fun_app$a (llist_all2$c ?v0 )(lCons$a ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))))):named a13 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 B$ )(?v4 B_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))(and (fun_app$d (fun_app$h ?v0 ?v1 )?v3 )(fun_app$ (llist_all2$ ?v0 ?v2 )?v4 ))):pattern ((fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))))):named a14 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )lNil$ )(= ?v1 lNil$ )):pattern ((fun_app$c (llist_all2$a ?v0 )?v1 )))):named a15 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ ))(! (= (fun_app$b (llist_all2$b ?v0 ?v1 )lNil$ )(= ?v1 lNil$a )):pattern ((llist_all2$b ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$c ?v0 )?v1 )lNil$a )(= ?v1 lNil$a )):pattern ((fun_app$a (llist_all2$c ?v0 )?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 ?v1 )lNil$a )(= ?v1 lNil$ )):pattern ((llist_all2$ ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$a ?v0 )lNil$ )?v1 )(= ?v1 lNil$ )):pattern ((fun_app$b (fun_app$c (llist_all2$a ?v0 )lNil$ )?v1 )))):named a19 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 A_llist$ ))(! (= (fun_app$b (llist_all2$b ?v0 lNil$a )?v1 )(= ?v1 lNil$ )):pattern ((fun_app$b (llist_all2$b ?v0 lNil$a )?v1 )))):named a20 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$c ?v0 )lNil$a )?v1 )(= ?v1 lNil$a )):pattern ((fun_app$ (fun_app$a (llist_all2$c ?v0 )lNil$a )?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 B_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 lNil$ )?v1 )(= ?v1 lNil$a )):pattern ((fun_app$ (llist_all2$ ?v0 lNil$ )?v1 )))):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 B$ )(?v3 B_llist$ ))(=> (and (= xs$ (lCons$ ?v0 ?v1 ))(and (= ys$ (lCons$a ?v2 ?v3 ))(and (fun_app$d (fun_app$h p$ ?v0 )?v2 )(fun_app$ (llist_all2$ p$ ?v1 )?v3 ))))thesis$ )):named a23 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 A_llist$ ))(= (fun_app$b (fun_app$c (llist_all2$a ?v0 )(lCons$ ?v1 ?v2 ))?v3 )(exists ((?v4 A$ )(?v5 A_llist$ ))(and (= ?v3 (lCons$ ?v4 ?v5 ))(and (fun_app$f (fun_app$g ?v0 ?v1 )?v4 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v2 )?v5 )))))):named a24 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ )(?v3 A_llist$ ))(= (fun_app$b (llist_all2$b ?v0 (lCons$a ?v1 ?v2 ))?v3 )(exists ((?v4 A$ )(?v5 A_llist$ ))(and (= ?v3 (lCons$ ?v4 ?v5 ))(and (fun_app$f (fun_app$i ?v0 ?v1 )?v4 )(fun_app$b (llist_all2$b ?v0 ?v2 )?v5 )))))):named a25 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ )(?v3 B_llist$ ))(= (fun_app$ (fun_app$a (llist_all2$c ?v0 )(lCons$a ?v1 ?v2 ))?v3 )(exists ((?v4 B$ )(?v5 B_llist$ ))(and (= ?v3 (lCons$a ?v4 ?v5 ))(and (fun_app$d (fun_app$e ?v0 ?v1 )?v4 )(fun_app$ (fun_app$a (llist_all2$c ?v0 )?v2 )?v5 )))))):named a26 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ )(?v3 B_llist$ ))(= (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))?v3 )(exists ((?v4 B$ )(?v5 B_llist$ ))(and (= ?v3 (lCons$a ?v4 ?v5 ))(and (fun_app$d (fun_app$h ?v0 ?v1 )?v4 )(fun_app$ (llist_all2$ ?v0 ?v2 )?v5 )))))):named a27 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )(lCons$ ?v2 ?v3 ))(exists ((?v4 A$ )(?v5 A_llist$ ))(and (= ?v1 (lCons$ ?v4 ?v5 ))(and (fun_app$f (fun_app$g ?v0 ?v4 )?v2 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v5 )?v3 )))))):named a28 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (fun_app$b (llist_all2$b ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(exists ((?v4 B$ )(?v5 B_llist$ ))(and (= ?v1 (lCons$a ?v4 ?v5 ))(and (fun_app$f (fun_app$i ?v0 ?v4 )?v2 )(fun_app$b (llist_all2$b ?v0 ?v5 )?v3 )))))):named a29 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (fun_app$ (fun_app$a (llist_all2$c ?v0 )?v1 )(lCons$a ?v2 ?v3 ))(exists ((?v4 B$ )(?v5 B_llist$ ))(and (= ?v1 (lCons$a ?v4 ?v5 ))(and (fun_app$d (fun_app$e ?v0 ?v4 )?v2 )(fun_app$ (fun_app$a (llist_all2$c ?v0 )?v5 )?v3 )))))):named a30 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B$ )(?v3 B_llist$ ))(= (fun_app$ (llist_all2$ ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(exists ((?v4 A$ )(?v5 A_llist$ ))(and (= ?v1 (lCons$ ?v4 ?v5 ))(and (fun_app$d (fun_app$h ?v0 ?v4 )?v2 )(fun_app$ (llist_all2$ ?v0 ?v5 )?v3 )))))):named a31 ))
(assert (! (forall ((?v0 A_llist$ ))(= (not (= ?v0 lNil$ ))(exists ((?v1 A$ )(?v2 A_llist$ ))(= ?v0 (lCons$ ?v1 ?v2 ))))):named a32 ))
(assert (! (forall ((?v0 B_llist$ ))(= (not (= ?v0 lNil$a ))(exists ((?v1 B$ )(?v2 B_llist$ ))(= ?v0 (lCons$a ?v1 ?v2 ))))):named a33 ))
(assert (! (= (llist_all2$c uu$ )uua$ ):named a34 ))
(assert (! (= (llist_all2$a uub$ )uuc$ ):named a35 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (= ?v0 lNil$ )false )(forall ((?v1 A$ )(?v2 A_llist$ ))(=> (= ?v0 (lCons$ ?v1 ?v2 ))false )))false )):named a36 ))
(assert (! (forall ((?v0 B_llist$ ))(=> (and (=> (= ?v0 lNil$a )false )(forall ((?v1 B$ )(?v2 B_llist$ ))(=> (= ?v0 (lCons$a ?v1 ?v2 ))false )))false )):named a37 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )?v2 )(and (=> (and (= ?v1 lNil$ )(= ?v2 lNil$ ))false )(forall ((?v3 A$ )(?v4 A_llist$ )(?v5 A$ )(?v6 A_llist$ ))(=> (and (= ?v1 (lCons$ ?v3 ?v4 ))(and (= ?v2 (lCons$ ?v5 ?v6 ))(and (fun_app$f (fun_app$g ?v0 ?v3 )?v5 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v4 )?v6 ))))false ))))false )):named a38 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ ))(=> (and (fun_app$b (llist_all2$b ?v0 ?v1 )?v2 )(and (=> (and (= ?v1 lNil$a )(= ?v2 lNil$ ))false )(forall ((?v3 B$ )(?v4 B_llist$ )(?v5 A$ )(?v6 A_llist$ ))(=> (and (= ?v1 (lCons$a ?v3 ?v4 ))(and (= ?v2 (lCons$ ?v5 ?v6 ))(and (fun_app$f (fun_app$i ?v0 ?v3 )?v5 )(fun_app$b (llist_all2$b ?v0 ?v4 )?v6 ))))false ))))false )):named a39 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0 )?v1 )?v2 )(and (=> (and (= ?v1 lNil$a )(= ?v2 lNil$a ))false )(forall ((?v3 B$ )(?v4 B_llist$ )(?v5 B$ )(?v6 B_llist$ ))(=> (and (= ?v1 (lCons$a ?v3 ?v4 ))(and (= ?v2 (lCons$a ?v5 ?v6 ))(and (fun_app$d (fun_app$e ?v0 ?v3 )?v5 )(fun_app$ (fun_app$a (llist_all2$c ?v0 )?v4 )?v6 ))))false ))))false )):named a40 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ ))(=> (and (fun_app$ (llist_all2$ ?v0 ?v1 )?v2 )(and (=> (and (= ?v1 lNil$ )(= ?v2 lNil$a ))false )(forall ((?v3 A$ )(?v4 A_llist$ )(?v5 B$ )(?v6 B_llist$ ))(=> (and (= ?v1 (lCons$ ?v3 ?v4 ))(and (= ?v2 (lCons$a ?v5 ?v6 ))(and (fun_app$d (fun_app$h ?v0 ?v3 )?v5 )(fun_app$ (llist_all2$ ?v0 ?v4 )?v6 ))))false ))))false )):named a41 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A$ )(?v3 A_llist$ )(?v4 A_llist$ ))(=> (and (fun_app$f (fun_app$g ?v0 ?v1 )?v2 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v3 )?v4 ))(fun_app$b (fun_app$c (llist_all2$a ?v0 )(lCons$ ?v1 ?v3 ))(lCons$ ?v2 ?v4 )))):named a42 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 A$ )(?v3 B_llist$ )(?v4 A_llist$ ))(=> (and (fun_app$f (fun_app$i ?v0 ?v1 )?v2 )(fun_app$b (llist_all2$b ?v0 ?v3 )?v4 ))(fun_app$b (llist_all2$b ?v0 (lCons$a ?v1 ?v3 ))(lCons$ ?v2 ?v4 )))):named a43 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B$ )(?v3 B_llist$ )(?v4 B_llist$ ))(=> (and (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(fun_app$ (fun_app$a (llist_all2$c ?v0 )?v3 )?v4 ))(fun_app$ (fun_app$a (llist_all2$c ?v0 )(lCons$a ?v1 ?v3 ))(lCons$a ?v2 ?v4 )))):named a44 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 B$ )(?v3 A_llist$ )(?v4 B_llist$ ))(=> (and (fun_app$d (fun_app$h ?v0 ?v1 )?v2 )(fun_app$ (llist_all2$ ?v0 ?v3 )?v4 ))(fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v3 ))(lCons$a ?v2 ?v4 )))):named a45 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(not (= lNil$ (lCons$ ?v0 ?v1 )))):named a46 ))
(assert (! (forall ((?v0 B$ )(?v1 B_llist$ ))(not (= lNil$a (lCons$a ?v0 ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(fun_app$b (fun_app$c (llist_all2$a ?v0 )lNil$ )lNil$ )):named a48 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ ))(fun_app$b (llist_all2$b ?v0 lNil$a )lNil$ )):named a49 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ ))(fun_app$ (fun_app$a (llist_all2$c ?v0 )lNil$a )lNil$a )):named a50 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ ))(fun_app$ (llist_all2$ ?v0 lNil$ )lNil$a )):named a51 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ ))(not (fun_app$b (fun_app$c (llist_all2$a ?v0 )(lCons$ ?v1 ?v2 ))lNil$ ))):named a52 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ ))(not (fun_app$b (llist_all2$b ?v0 (lCons$a ?v1 ?v2 ))lNil$ ))):named a53 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B_llist$ ))(not (fun_app$ (fun_app$a (llist_all2$c ?v0 )(lCons$a ?v1 ?v2 ))lNil$a ))):named a54 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 A_llist$ ))(not (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))lNil$a ))):named a55 ))
(check-sat )
;(get-unsat-core )
