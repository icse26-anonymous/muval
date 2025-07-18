;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort Nat_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort B_llist_bool_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort B_stream_bool_fun$ 0 )
(declare-sort A_llist_a_llist_bool_fun_fun$ 0 )
(declare-sort B_llist_b_llist_bool_fun_fun$ 0 )
(declare-sort A_stream_a_stream_bool_fun_fun$ 0 )
(declare-sort B_stream_b_stream_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(B_llist$ (lNil$a )(lCons$a (lhd$a B$ )(ltl$a B_llist$ )))(A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))(B_stream$ (sCons$a (shd$a B$ )(stl$a B_stream$ )))))
(declare-fun p$ ()A_b_bool_fun_fun$ )
(declare-fun uu$ ()B_b_bool_fun_fun$ )
(declare-fun xs$ ()A_stream$ )
(declare-fun ys$ ()B_stream$ )
(declare-fun uua$ ()B_stream_b_stream_bool_fun_fun$ )
(declare-fun uub$ ()A_a_bool_fun_fun$ )
(declare-fun uuc$ ()A_stream_a_stream_bool_fun_fun$ )
(declare-fun uud$ ()A_llist_a_llist_bool_fun_fun$ )
(declare-fun uue$ ()B_llist_b_llist_bool_fun_fun$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun lnull$a (B_llist$ )Bool )
(declare-fun transp$ (A_a_bool_fun_fun$ )Bool )
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$ )Bool )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun transp$a (B_b_bool_fun_fun$ )Bool )
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$ )B_llist_bool_fun$ )
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$ )A_llist_bool_fun$ )
(declare-fun fun_app$d (B_stream_bool_fun$ B_stream$ )Bool )
(declare-fun fun_app$e (B_stream_b_stream_bool_fun_fun$ B_stream$ )B_stream_bool_fun$ )
(declare-fun fun_app$f (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$g (A_stream_a_stream_bool_fun_fun$ A_stream$ )A_stream_bool_fun$ )
(declare-fun fun_app$h (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$i (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$j (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$l (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun fun_app$m (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$n (Nat_b_fun$ Nat$ )B$ )
(declare-fun fun_app$o (Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$p (A_a_fun$ A$ )A$ )
(declare-fun fun_app$q (B_b_fun$ B$ )B$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(declare-fun lfinite$a (B_llist$ )Bool )
(declare-fun siterate$ (A_a_fun$ A$ )A_stream$ )
(declare-fun inf_llist$ (Nat_b_fun$ )B_llist$ )
(declare-fun iterates$a (B_b_fun$ B$ )B_llist$ )
(declare-fun siterate$a (B_b_fun$ B$ )B_stream$ )
(declare-fun inf_llist$a (Nat_a_fun$ )A_llist$ )
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$ B_llist$ )Bool )
(declare-fun llist_all2$a (A_a_bool_fun_fun$ )A_llist_a_llist_bool_fun_fun$ )
(declare-fun llist_all2$b (B_b_bool_fun_fun$ )B_llist_b_llist_bool_fun_fun$ )
(declare-fun llist_all2$c (B_a_bool_fun_fun$ B_llist$ A_llist$ )Bool )
(declare-fun stream_all2$ (A_b_bool_fun_fun$ A_stream$ B_stream$ )Bool )
(declare-fun stream_all2$a (B_b_bool_fun_fun$ )B_stream_b_stream_bool_fun_fun$ )
(declare-fun stream_all2$b (A_a_bool_fun_fun$ )A_stream_a_stream_bool_fun_fun$ )
(declare-fun stream_all2$c (B_a_bool_fun_fun$ B_stream$ A_stream$ )Bool )
(declare-fun llist_of_stream$ (A_stream$ )A_llist$ )
(declare-fun stream_of_llist$ (A_llist$ )A_stream$ )
(declare-fun llist_of_stream$a (B_stream$ )B_llist$ )
(declare-fun stream_of_llist$a (B_llist$ )B_stream$ )
(assert (! (forall ((?v0 B_llist$ )(?v1 B_llist$ ))(! (= (fun_app$ (fun_app$a uue$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uue$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(! (= (fun_app$b (fun_app$c uud$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uud$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 B_stream$ )(?v1 B_stream$ ))(! (= (fun_app$d (fun_app$e uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uua$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(! (= (fun_app$f (fun_app$g uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (fun_app$g uuc$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$h (fun_app$i uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$h (fun_app$i uu$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$j (fun_app$k uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$j (fun_app$k uub$ ?v0 )?v1 )))):named a5 ))
(assert (! (not (= (llist_all2$ p$ (llist_of_stream$ xs$ )(llist_of_stream$a ys$ ))(stream_all2$ p$ xs$ ys$ ))):named a6 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(= (= (llist_of_stream$ ?v0 )(llist_of_stream$ ?v1 ))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 B_stream$ )(?v1 B_stream$ ))(= (= (llist_of_stream$a ?v0 )(llist_of_stream$a ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (= (stream_all2$a uu$ )uua$ ):named a9 ))
(assert (! (= (stream_all2$b uub$ )uuc$ ):named a10 ))
(assert (! (= (llist_all2$a uub$ )uud$ ):named a11 ))
(assert (! (= (llist_all2$b uu$ )uue$ ):named a12 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_llist$ )(?v2 A_llist$ )(?v3 B_a_bool_fun_fun$ ))(=> (and (llist_all2$c ?v0 ?v1 ?v2 )(forall ((?v4 B$ )(?v5 A$ ))(=> (fun_app$j (fun_app$l ?v0 ?v4 )?v5 )(fun_app$j (fun_app$l ?v3 ?v4 )?v5 ))))(llist_all2$c ?v3 ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )?v2 )(forall ((?v4 A$ )(?v5 A$ ))(=> (fun_app$j (fun_app$k ?v0 ?v4 )?v5 )(fun_app$j (fun_app$k ?v3 ?v4 )?v5 ))))(fun_app$b (fun_app$c (llist_all2$a ?v3 )?v1 )?v2 ))):named a14 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_b_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$b ?v0 )?v1 )?v2 )(forall ((?v4 B$ )(?v5 B$ ))(=> (fun_app$h (fun_app$i ?v0 ?v4 )?v5 )(fun_app$h (fun_app$i ?v3 ?v4 )?v5 ))))(fun_app$ (fun_app$a (llist_all2$b ?v3 )?v1 )?v2 ))):named a15 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_llist$ )(?v2 B_llist$ )(?v3 A_b_bool_fun_fun$ ))(=> (and (llist_all2$ ?v0 ?v1 ?v2 )(forall ((?v4 A$ )(?v5 B$ ))(=> (fun_app$h (fun_app$m ?v0 ?v4 )?v5 )(fun_app$h (fun_app$m ?v3 ?v4 )?v5 ))))(llist_all2$ ?v3 ?v1 ?v2 ))):named a16 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A_a_bool_fun_fun$ )(?v3 B_llist$ )(?v4 A_llist$ )(?v5 B_llist$ )(?v6 A_llist$ ))(=> (and (forall ((?v7 B$ )(?v8 A$ ))(=> (fun_app$j (fun_app$l ?v0 ?v7 )?v8 )(forall ((?v9 B$ )(?v10 A$ ))(=> (fun_app$j (fun_app$l ?v0 ?v9 )?v10 )(= (fun_app$h (fun_app$i ?v1 ?v7 )?v9 )(fun_app$j (fun_app$k ?v2 ?v8 )?v10 ))))))(and (llist_all2$c ?v0 ?v3 ?v4 )(llist_all2$c ?v0 ?v5 ?v6 )))(= (fun_app$ (fun_app$a (llist_all2$b ?v1 )?v3 )?v5 )(fun_app$b (fun_app$c (llist_all2$a ?v2 )?v4 )?v6 )))):named a17 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 A_a_bool_fun_fun$ )(?v3 A_llist$ )(?v4 A_llist$ )(?v5 A_llist$ )(?v6 A_llist$ ))(=> (and (forall ((?v7 A$ )(?v8 A$ ))(=> (fun_app$j (fun_app$k ?v0 ?v7 )?v8 )(forall ((?v9 A$ )(?v10 A$ ))(=> (fun_app$j (fun_app$k ?v0 ?v9 )?v10 )(= (fun_app$j (fun_app$k ?v1 ?v7 )?v9 )(fun_app$j (fun_app$k ?v2 ?v8 )?v10 ))))))(and (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v3 )?v4 )(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v5 )?v6 )))(= (fun_app$b (fun_app$c (llist_all2$a ?v1 )?v3 )?v5 )(fun_app$b (fun_app$c (llist_all2$a ?v2 )?v4 )?v6 )))):named a18 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_b_bool_fun_fun$ )(?v3 B_llist$ )(?v4 B_llist$ )(?v5 B_llist$ )(?v6 B_llist$ ))(=> (and (forall ((?v7 B$ )(?v8 B$ ))(=> (fun_app$h (fun_app$i ?v0 ?v7 )?v8 )(forall ((?v9 B$ )(?v10 B$ ))(=> (fun_app$h (fun_app$i ?v0 ?v9 )?v10 )(= (fun_app$h (fun_app$i ?v1 ?v7 )?v9 )(fun_app$h (fun_app$i ?v2 ?v8 )?v10 ))))))(and (fun_app$ (fun_app$a (llist_all2$b ?v0 )?v3 )?v4 )(fun_app$ (fun_app$a (llist_all2$b ?v0 )?v5 )?v6 )))(= (fun_app$ (fun_app$a (llist_all2$b ?v1 )?v3 )?v5 )(fun_app$ (fun_app$a (llist_all2$b ?v2 )?v4 )?v6 )))):named a19 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 B_b_bool_fun_fun$ )(?v3 A_llist$ )(?v4 B_llist$ )(?v5 A_llist$ )(?v6 B_llist$ ))(=> (and (forall ((?v7 A$ )(?v8 B$ ))(=> (fun_app$h (fun_app$m ?v0 ?v7 )?v8 )(forall ((?v9 A$ )(?v10 B$ ))(=> (fun_app$h (fun_app$m ?v0 ?v9 )?v10 )(= (fun_app$j (fun_app$k ?v1 ?v7 )?v9 )(fun_app$h (fun_app$i ?v2 ?v8 )?v10 ))))))(and (llist_all2$ ?v0 ?v3 ?v4 )(llist_all2$ ?v0 ?v5 ?v6 )))(= (fun_app$b (fun_app$c (llist_all2$a ?v1 )?v3 )?v5 )(fun_app$ (fun_app$a (llist_all2$b ?v2 )?v4 )?v6 )))):named a20 ))
(assert (! (forall ((?v0 A_stream$ ))(= (stream_of_llist$ (llist_of_stream$ ?v0 ))?v0 )):named a21 ))
(assert (! (forall ((?v0 B_stream$ ))(= (stream_of_llist$a (llist_of_stream$a ?v0 ))?v0 )):named a22 ))
(assert (! (forall ((?v0 A_stream$ ))(= (stream_of_llist$ (llist_of_stream$ ?v0 ))?v0 )):named a23 ))
(assert (! (forall ((?v0 B_stream$ ))(= (stream_of_llist$a (llist_of_stream$a ?v0 ))?v0 )):named a24 ))
(assert (! (forall ((?v0 A_stream$ ))(not (lnull$ (llist_of_stream$ ?v0 )))):named a25 ))
(assert (! (forall ((?v0 B_stream$ ))(not (lnull$a (llist_of_stream$a ?v0 )))):named a26 ))
(assert (! (forall ((?v0 A_stream$ ))(not (lfinite$ (llist_of_stream$ ?v0 )))):named a27 ))
(assert (! (forall ((?v0 B_stream$ ))(not (lfinite$a (llist_of_stream$a ?v0 )))):named a28 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 Nat_b_fun$ )(?v2 Nat_a_fun$ ))(= (llist_all2$c ?v0 (inf_llist$ ?v1 )(inf_llist$a ?v2 ))(forall ((?v3 Nat$ ))(fun_app$j (fun_app$l ?v0 (fun_app$n ?v1 ?v3 ))(fun_app$o ?v2 ?v3 ))))):named a29 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 Nat_a_fun$ )(?v2 Nat_a_fun$ ))(= (fun_app$b (fun_app$c (llist_all2$a ?v0 )(inf_llist$a ?v1 ))(inf_llist$a ?v2 ))(forall ((?v3 Nat$ ))(fun_app$j (fun_app$k ?v0 (fun_app$o ?v1 ?v3 ))(fun_app$o ?v2 ?v3 ))))):named a30 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 Nat_b_fun$ )(?v2 Nat_b_fun$ ))(= (fun_app$ (fun_app$a (llist_all2$b ?v0 )(inf_llist$ ?v1 ))(inf_llist$ ?v2 ))(forall ((?v3 Nat$ ))(fun_app$h (fun_app$i ?v0 (fun_app$n ?v1 ?v3 ))(fun_app$n ?v2 ?v3 ))))):named a31 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 Nat_a_fun$ )(?v2 Nat_b_fun$ ))(= (llist_all2$ ?v0 (inf_llist$a ?v1 )(inf_llist$ ?v2 ))(forall ((?v3 Nat$ ))(fun_app$h (fun_app$m ?v0 (fun_app$o ?v1 ?v3 ))(fun_app$n ?v2 ?v3 ))))):named a32 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (fun_app$f (fun_app$g (stream_all2$b ?v0 )(sCons$ ?v1 ?v2 ))(sCons$ ?v3 ?v4 ))(and (fun_app$j (fun_app$k ?v0 ?v1 )?v3 )(fun_app$f (fun_app$g (stream_all2$b ?v0 )?v2 )?v4 ))):pattern ((fun_app$f (fun_app$g (stream_all2$b ?v0 )(sCons$ ?v1 ?v2 ))(sCons$ ?v3 ?v4 ))))):named a33 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (stream_all2$c ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))(and (fun_app$j (fun_app$l ?v0 ?v1 )?v3 )(stream_all2$c ?v0 ?v2 ?v4 ))):pattern ((stream_all2$c ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))))):named a34 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (fun_app$d (fun_app$e (stream_all2$a ?v0 )(sCons$a ?v1 ?v2 ))(sCons$a ?v3 ?v4 ))(and (fun_app$h (fun_app$i ?v0 ?v1 )?v3 )(fun_app$d (fun_app$e (stream_all2$a ?v0 )?v2 )?v4 ))):pattern ((fun_app$d (fun_app$e (stream_all2$a ?v0 )(sCons$a ?v1 ?v2 ))(sCons$a ?v3 ?v4 ))))):named a35 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (stream_all2$ ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))(and (fun_app$h (fun_app$m ?v0 ?v1 )?v3 )(stream_all2$ ?v0 ?v2 ?v4 ))):pattern ((stream_all2$ ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))))):named a36 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (llist_of_stream$ (siterate$ ?v0 ?v1 ))(iterates$ ?v0 ?v1 ))):named a37 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (llist_of_stream$a (siterate$a ?v0 ?v1 ))(iterates$a ?v0 ?v1 ))):named a38 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_llist$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )?v2 )(and (fun_app$b (fun_app$c (llist_all2$a ?v0 )?v2 )?v3 )(transp$ ?v0 )))(fun_app$b (fun_app$c (llist_all2$a ?v0 )?v1 )?v3 ))):named a39 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_llist$ )(?v2 B_llist$ )(?v3 B_llist$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$b ?v0 )?v1 )?v2 )(and (fun_app$ (fun_app$a (llist_all2$b ?v0 )?v2 )?v3 )(transp$a ?v0 )))(fun_app$ (fun_app$a (llist_all2$b ?v0 )?v1 )?v3 ))):named a40 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ )(?v3 A_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a41 ))
(assert (! (forall ((?v0 B$ )(?v1 B_stream$ )(?v2 B$ )(?v3 B_stream$ ))(= (= (sCons$a ?v0 ?v1 )(sCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a42 ))
(assert (! (forall ((?v0 Nat_a_fun$ )(?v1 Nat_a_fun$ ))(= (= (inf_llist$a ?v0 )(inf_llist$a ?v1 ))(= ?v0 ?v1 ))):named a43 ))
(assert (! (forall ((?v0 Nat_b_fun$ )(?v1 Nat_b_fun$ ))(= (= (inf_llist$ ?v0 )(inf_llist$ ?v1 ))(= ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (not (lfinite$ ?v0 ))(= (llist_of_stream$ (stream_of_llist$ ?v0 ))?v0 ))):named a45 ))
(assert (! (forall ((?v0 B_llist$ ))(=> (not (lfinite$a ?v0 ))(= (llist_of_stream$a (stream_of_llist$a ?v0 ))?v0 ))):named a46 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (siterate$ ?v0 ?v1 )(sCons$ ?v1 (siterate$ ?v0 (fun_app$p ?v0 ?v1 ))))):named a47 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (siterate$a ?v0 ?v1 )(sCons$a ?v1 (siterate$a ?v0 (fun_app$q ?v0 ?v1 ))))):named a48 ))
(check-sat )
;(get-unsat-core )
