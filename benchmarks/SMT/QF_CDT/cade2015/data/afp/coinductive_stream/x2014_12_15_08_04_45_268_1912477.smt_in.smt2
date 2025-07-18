;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun$ 0 )
(declare-sort A_b_b_fun_fun$ 0 )
(declare-sort B_a_a_fun_fun$ 0 )
(declare-sort B_a_b_fun_fun$ 0 )
(declare-sort B_b_a_fun_fun$ 0 )
(declare-sort B_b_b_fun_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort B_stream_bool_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-sort B_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun shd$a (B_stream$)B$)
(declare-fun stl$a (B_stream$)B_stream$)
(declare-fun sCons$a (B$ B_stream$ )B_stream$)
(declare-fun f$ ()B_a_fun$ )
(declare-fun y$ ()A$ )
(declare-fun xs$ ()B_stream$ )
(declare-fun ys$ ()A_stream$ )
(declare-fun hld$ (A_set$ )A_stream_bool_fun$ )
(declare-fun hld$a (B_set$ )B_stream_bool_fun$ )
(declare-fun smap$ (B_a_fun$ B_stream$ )A_stream$ )
(declare-fun snth$ (B_stream$ Nat$ )B$ )
(declare-fun sset$ (B_stream$ )B_set$ )
(declare-fun sdrop$ (Nat$ B_stream$ )B_stream$ )
(declare-fun smap$a (A_a_fun$ A_stream$ )A_stream$ )
(declare-fun smap$b (A_b_fun$ A_stream$ )B_stream$ )
(declare-fun smap$c (B_b_fun$ B_stream$ )B_stream$ )
(declare-fun smap2$ (A_a_a_fun_fun$ A_stream$ A_stream$ )A_stream$ )
(declare-fun snth$a (A_stream$ Nat$ )A$ )
(declare-fun sset$a (A_stream$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun sdrop$a (Nat$ A_stream$ )A_stream$ )
(declare-fun smap2$a (A_a_b_fun_fun$ A_stream$ A_stream$ )B_stream$ )
(declare-fun smap2$b (A_b_a_fun_fun$ A_stream$ B_stream$ )A_stream$ )
(declare-fun smap2$c (A_b_b_fun_fun$ A_stream$ B_stream$ )B_stream$ )
(declare-fun smap2$d (B_a_a_fun_fun$ B_stream$ A_stream$ )A_stream$ )
(declare-fun smap2$e (B_a_b_fun_fun$ B_stream$ A_stream$ )B_stream$ )
(declare-fun smap2$f (B_b_a_fun_fun$ B_stream$ B_stream$ )A_stream$ )
(declare-fun smap2$g (B_b_b_fun_fun$ B_stream$ B_stream$ )B_stream$ )
(declare-fun vimage$ (B_b_fun$ B_set$ )B_set$ )
(declare-fun fun_app$ (B_a_fun$ B$ )A$ )
(declare-fun member$a (B$ B_set$ )Bool )
(declare-fun sfilter$ (A_bool_fun$ A_stream$ )A_stream$ )
(declare-fun smember$ (A$ )A_stream_bool_fun$ )
(declare-fun vimage$a (A_b_fun$ B_set$ )A_set$ )
(declare-fun vimage$b (A_a_fun$ A_set$ )A_set$ )
(declare-fun vimage$c (B_a_fun$ A_set$ )B_set$ )
(declare-fun fun_app$a (A_a_fun$ A$ )A$ )
(declare-fun fun_app$b (A_b_fun$ A$ )B$ )
(declare-fun fun_app$c (B_b_fun$ B$ )B$ )
(declare-fun fun_app$d (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$e (B_stream_bool_fun$ B_stream$ )Bool )
(declare-fun fun_app$f (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$g (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$h (A_a_a_fun_fun$ A$ )A_a_fun$ )
(declare-fun fun_app$i (A_a_b_fun_fun$ A$ )A_b_fun$ )
(declare-fun fun_app$j (A_b_a_fun_fun$ A$ )B_a_fun$ )
(declare-fun fun_app$k (A_b_b_fun_fun$ A$ )B_b_fun$ )
(declare-fun fun_app$l (B_a_a_fun_fun$ B$ )A_a_fun$ )
(declare-fun fun_app$m (B_a_b_fun_fun$ B$ )A_b_fun$ )
(declare-fun fun_app$n (B_b_a_fun_fun$ B$ )B_a_fun$ )
(declare-fun fun_app$o (B_b_b_fun_fun$ B$ )B_b_fun$ )
(declare-fun sfilter$a (B_bool_fun$ B_stream$ )B_stream$ )
(declare-fun smember$a (B$ )B_stream_bool_fun$ )
(declare-fun streamsp$ (A_bool_fun$ )A_stream_bool_fun$ )
(declare-fun streamsp$a (B_bool_fun$ )B_stream_bool_fun$ )
(declare-fun stream_all$ (A_bool_fun$ )A_stream_bool_fun$ )
(declare-fun pred_stream$ (A_bool_fun$ )A_stream_bool_fun$ )
(declare-fun sdrop_while$ (A_bool_fun$ A_stream$ )A_stream$ )
(declare-fun sinterleave$ (A_stream$ A_stream$ )A_stream$ )
(declare-fun stream_all$a (B_bool_fun$ )B_stream_bool_fun$ )
(declare-fun pred_stream$a (B_bool_fun$ )B_stream_bool_fun$ )
(declare-fun sdrop_while$a (B_bool_fun$ B_stream$ )B_stream$ )
(declare-fun sinterleave$a (B_stream$ B_stream$ )B_stream$ )
(assert (! (not (= (= (smap$ f$ xs$ )(sCons$ y$ ys$ ))(exists ((?v0 B$ )(?v1 B_stream$ ))(and (= xs$ (sCons$a ?v0 ?v1 ))(and (= y$ (fun_app$ f$ ?v0 ))(= ys$ (smap$ f$ ?v1 ))))))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ )(?v3 A_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a1 ))
(assert (! (forall ((?v0 B$ )(?v1 B_stream$ )(?v2 B$ )(?v3 B_stream$ ))(= (= (sCons$a ?v0 ?v1 )(sCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a2 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (smap$a ?v0 (sCons$ ?v1 ?v2 ))(sCons$ (fun_app$a ?v0 ?v1 )(smap$a ?v0 ?v2 ))):pattern ((smap$a ?v0 (sCons$ ?v1 ?v2 ))))):named a3 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (smap$b ?v0 (sCons$ ?v1 ?v2 ))(sCons$a (fun_app$b ?v0 ?v1 )(smap$b ?v0 ?v2 ))):pattern ((smap$b ?v0 (sCons$ ?v1 ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (smap$ ?v0 (sCons$a ?v1 ?v2 ))(sCons$ (fun_app$ ?v0 ?v1 )(smap$ ?v0 ?v2 ))):pattern ((smap$ ?v0 (sCons$a ?v1 ?v2 ))))):named a5 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (smap$c ?v0 (sCons$a ?v1 ?v2 ))(sCons$a (fun_app$c ?v0 ?v1 )(smap$c ?v0 ?v2 ))):pattern ((smap$c ?v0 (sCons$a ?v1 ?v2 ))))):named a6 ))
(assert (! (forall ((?v0 A_stream$ ))(=> (forall ((?v1 A$ )(?v2 A_stream$ ))(=> (= ?v0 (sCons$ ?v1 ?v2 ))false ))false )):named a7 ))
(assert (! (forall ((?v0 B_stream$ ))(=> (forall ((?v1 B$ )(?v2 B_stream$ ))(=> (= ?v0 (sCons$a ?v1 ?v2 ))false ))false )):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (fun_app$d (smember$ ?v0 )(sCons$ ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (fun_app$d (smember$ ?v0 )?v2 ))):pattern ((fun_app$d (smember$ ?v0 )(sCons$ ?v1 ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (fun_app$e (smember$a ?v0 )(sCons$a ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (fun_app$e (smember$a ?v0 )?v2 ))):pattern ((fun_app$e (smember$a ?v0 )(sCons$a ?v1 ?v2 ))))):named a10 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (fun_app$d (pred_stream$ ?v0 )(sCons$ ?v1 ?v2 ))(and (fun_app$f ?v0 ?v1 )(fun_app$d (pred_stream$ ?v0 )?v2 ))):pattern ((fun_app$d (pred_stream$ ?v0 )(sCons$ ?v1 ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (fun_app$e (pred_stream$a ?v0 )(sCons$a ?v1 ?v2 ))(and (fun_app$g ?v0 ?v1 )(fun_app$e (pred_stream$a ?v0 )?v2 ))):pattern ((fun_app$e (pred_stream$a ?v0 )(sCons$a ?v1 ?v2 ))))):named a12 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (fun_app$d (stream_all$ ?v0 )(sCons$ ?v1 ?v2 ))(and (fun_app$f ?v0 ?v1 )(fun_app$d (stream_all$ ?v0 )?v2 ))):pattern ((fun_app$d (stream_all$ ?v0 )(sCons$ ?v1 ?v2 ))))):named a13 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (fun_app$e (stream_all$a ?v0 )(sCons$a ?v1 ?v2 ))(and (fun_app$g ?v0 ?v1 )(fun_app$e (stream_all$a ?v0 )?v2 ))):pattern ((fun_app$e (stream_all$a ?v0 )(sCons$a ?v1 ?v2 ))))):named a14 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$d (streamsp$ ?v0 )?v1 )(exists ((?v2 A$ )(?v3 A_stream$ ))(and (= ?v1 (sCons$ ?v2 ?v3 ))(and (fun_app$f ?v0 ?v2 )(fun_app$d (streamsp$ ?v0 )?v3 )))))):named a15 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_stream$ ))(= (fun_app$e (streamsp$a ?v0 )?v1 )(exists ((?v2 B$ )(?v3 B_stream$ ))(and (= ?v1 (sCons$a ?v2 ?v3 ))(and (fun_app$g ?v0 ?v2 )(fun_app$e (streamsp$a ?v0 )?v3 )))))):named a16 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(=> (and (fun_app$d (streamsp$ ?v0 )?v1 )(forall ((?v2 A$ )(?v3 A_stream$ ))(=> (and (= ?v1 (sCons$ ?v2 ?v3 ))(and (fun_app$f ?v0 ?v2 )(fun_app$d (streamsp$ ?v0 )?v3 )))false )))false )):named a17 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_stream$ ))(=> (and (fun_app$e (streamsp$a ?v0 )?v1 )(forall ((?v2 B$ )(?v3 B_stream$ ))(=> (and (= ?v1 (sCons$a ?v2 ?v3 ))(and (fun_app$g ?v0 ?v2 )(fun_app$e (streamsp$a ?v0 )?v3 )))false )))false )):named a18 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ )(?v2 A_bool_fun$ ))(=> (and (fun_app$d ?v0 ?v1 )(forall ((?v3 A_stream$ ))(=> (fun_app$d ?v0 ?v3 )(exists ((?v4 A$ )(?v5 A_stream$ ))(and (= ?v3 (sCons$ ?v4 ?v5 ))(and (fun_app$f ?v2 ?v4 )(or (fun_app$d ?v0 ?v5 )(fun_app$d (streamsp$ ?v2 )?v5 ))))))))(fun_app$d (streamsp$ ?v2 )?v1 ))):named a19 ))
(assert (! (forall ((?v0 B_stream_bool_fun$ )(?v1 B_stream$ )(?v2 B_bool_fun$ ))(=> (and (fun_app$e ?v0 ?v1 )(forall ((?v3 B_stream$ ))(=> (fun_app$e ?v0 ?v3 )(exists ((?v4 B$ )(?v5 B_stream$ ))(and (= ?v3 (sCons$a ?v4 ?v5 ))(and (fun_app$g ?v2 ?v4 )(or (fun_app$e ?v0 ?v5 )(fun_app$e (streamsp$a ?v2 )?v5 ))))))))(fun_app$e (streamsp$a ?v2 )?v1 ))):named a20 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (fun_app$d (hld$ ?v0 )(sCons$ ?v1 ?v2 ))(member$ ?v1 ?v0 )):pattern ((fun_app$d (hld$ ?v0 )(sCons$ ?v1 ?v2 ))))):named a21 ))
(assert (! (forall ((?v0 B_set$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (fun_app$e (hld$a ?v0 )(sCons$a ?v1 ?v2 ))(member$a ?v1 ?v0 )):pattern ((fun_app$e (hld$a ?v0 )(sCons$a ?v1 ?v2 ))))):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A_stream$ ))(! (= (sinterleave$ (sCons$ ?v0 ?v1 )?v2 )(sCons$ ?v0 (sinterleave$ ?v2 ?v1 ))):pattern ((sinterleave$ (sCons$ ?v0 ?v1 )?v2 )))):named a23 ))
(assert (! (forall ((?v0 B$ )(?v1 B_stream$ )(?v2 B_stream$ ))(! (= (sinterleave$a (sCons$a ?v0 ?v1 )?v2 )(sCons$a ?v0 (sinterleave$a ?v2 ?v1 ))):pattern ((sinterleave$a (sCons$a ?v0 ?v1 )?v2 )))):named a24 ))
(assert (! (forall ((?v0 B_set$ )(?v1 B_b_fun$ )(?v2 B_stream$ ))(= (fun_app$e (hld$a ?v0 )(smap$c ?v1 ?v2 ))(fun_app$e (hld$a (vimage$ ?v1 ?v0 ))?v2 ))):named a25 ))
(assert (! (forall ((?v0 B_set$ )(?v1 A_b_fun$ )(?v2 A_stream$ ))(= (fun_app$e (hld$a ?v0 )(smap$b ?v1 ?v2 ))(fun_app$d (hld$ (vimage$a ?v1 ?v0 ))?v2 ))):named a26 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_a_fun$ )(?v2 A_stream$ ))(= (fun_app$d (hld$ ?v0 )(smap$a ?v1 ?v2 ))(fun_app$d (hld$ (vimage$b ?v1 ?v0 ))?v2 ))):named a27 ))
(assert (! (forall ((?v0 A_set$ )(?v1 B_a_fun$ )(?v2 B_stream$ ))(= (fun_app$d (hld$ ?v0 )(smap$ ?v1 ?v2 ))(fun_app$e (hld$a (vimage$c ?v1 ?v0 ))?v2 ))):named a28 ))
(assert (! (forall ((?v0 B$ )(?v1 B_stream$ ))(! (= (fun_app$e (smember$a ?v0 )?v1 )(member$a ?v0 (sset$ ?v1 ))):pattern ((fun_app$e (smember$a ?v0 )?v1 )))):named a29 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (fun_app$d (smember$ ?v0 )?v1 )(member$ ?v0 (sset$a ?v1 ))):pattern ((fun_app$d (smember$ ?v0 )?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (sdrop_while$ ?v0 (sCons$ ?v1 ?v2 ))(ite (fun_app$f ?v0 ?v1 )(sdrop_while$ ?v0 ?v2 )(sCons$ ?v1 ?v2 ))):pattern ((sdrop_while$ ?v0 (sCons$ ?v1 ?v2 ))))):named a31 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (sdrop_while$a ?v0 (sCons$a ?v1 ?v2 ))(ite (fun_app$g ?v0 ?v1 )(sdrop_while$a ?v0 ?v2 )(sCons$a ?v1 ?v2 ))):pattern ((sdrop_while$a ?v0 (sCons$a ?v1 ?v2 ))))):named a32 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (smap2$ ?v0 (sCons$ ?v1 ?v2 )(sCons$ ?v3 ?v4 ))(sCons$ (fun_app$a (fun_app$h ?v0 ?v1 )?v3 )(smap2$ ?v0 ?v2 ?v4 ))):pattern ((smap2$ ?v0 (sCons$ ?v1 ?v2 )(sCons$ ?v3 ?v4 ))))):named a33 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (smap2$a ?v0 (sCons$ ?v1 ?v2 )(sCons$ ?v3 ?v4 ))(sCons$a (fun_app$b (fun_app$i ?v0 ?v1 )?v3 )(smap2$a ?v0 ?v2 ?v4 ))):pattern ((smap2$a ?v0 (sCons$ ?v1 ?v2 )(sCons$ ?v3 ?v4 ))))):named a34 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (smap2$b ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))(sCons$ (fun_app$ (fun_app$j ?v0 ?v1 )?v3 )(smap2$b ?v0 ?v2 ?v4 ))):pattern ((smap2$b ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))))):named a35 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ )(?v1 A$ )(?v2 A_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (smap2$c ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))(sCons$a (fun_app$c (fun_app$k ?v0 ?v1 )?v3 )(smap2$c ?v0 ?v2 ?v4 ))):pattern ((smap2$c ?v0 (sCons$ ?v1 ?v2 )(sCons$a ?v3 ?v4 ))))):named a36 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (smap2$d ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))(sCons$ (fun_app$a (fun_app$l ?v0 ?v1 )?v3 )(smap2$d ?v0 ?v2 ?v4 ))):pattern ((smap2$d ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))))):named a37 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 A$ )(?v4 A_stream$ ))(! (= (smap2$e ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))(sCons$a (fun_app$b (fun_app$m ?v0 ?v1 )?v3 )(smap2$e ?v0 ?v2 ?v4 ))):pattern ((smap2$e ?v0 (sCons$a ?v1 ?v2 )(sCons$ ?v3 ?v4 ))))):named a38 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (smap2$f ?v0 (sCons$a ?v1 ?v2 )(sCons$a ?v3 ?v4 ))(sCons$ (fun_app$ (fun_app$n ?v0 ?v1 )?v3 )(smap2$f ?v0 ?v2 ?v4 ))):pattern ((smap2$f ?v0 (sCons$a ?v1 ?v2 )(sCons$a ?v3 ?v4 ))))):named a39 ))
(assert (! (forall ((?v0 B_b_b_fun_fun$ )(?v1 B$ )(?v2 B_stream$ )(?v3 B$ )(?v4 B_stream$ ))(! (= (smap2$g ?v0 (sCons$a ?v1 ?v2 )(sCons$a ?v3 ?v4 ))(sCons$a (fun_app$c (fun_app$o ?v0 ?v1 )?v3 )(smap2$g ?v0 ?v2 ?v4 ))):pattern ((smap2$g ?v0 (sCons$a ?v1 ?v2 )(sCons$a ?v3 ?v4 ))))):named a40 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_b_fun$ )(?v2 B_stream$ ))(= (sdrop$ ?v0 (smap$c ?v1 ?v2 ))(smap$c ?v1 (sdrop$ ?v0 ?v2 )))):named a41 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_fun$ )(?v2 A_stream$ ))(= (sdrop$ ?v0 (smap$b ?v1 ?v2 ))(smap$b ?v1 (sdrop$a ?v0 ?v2 )))):named a42 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A_stream$ ))(= (sdrop$a ?v0 (smap$a ?v1 ?v2 ))(smap$a ?v1 (sdrop$a ?v0 ?v2 )))):named a43 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_a_fun$ )(?v2 B_stream$ ))(= (sdrop$a ?v0 (smap$ ?v1 ?v2 ))(smap$ ?v1 (sdrop$ ?v0 ?v2 )))):named a44 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_stream$ ))(= (fun_app$e (stream_all$a ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$g ?v0 (snth$ ?v1 ?v2 ))))):named a45 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$d (stream_all$ ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$f ?v0 (snth$a ?v1 ?v2 ))))):named a46 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_stream$ )(?v2 Nat$ ))(= (snth$ (smap$c ?v0 ?v1 )?v2 )(fun_app$c ?v0 (snth$ ?v1 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$ (smap$b ?v0 ?v1 )?v2 )(fun_app$b ?v0 (snth$a ?v1 ?v2 )))):named a48 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$a (smap$a ?v0 ?v1 )?v2 )(fun_app$a ?v0 (snth$a ?v1 ?v2 )))):named a49 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_stream$ )(?v2 Nat$ ))(= (snth$a (smap$ ?v0 ?v1 )?v2 )(fun_app$ ?v0 (snth$ ?v1 ?v2 )))):named a50 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (sfilter$ ?v0 (sCons$ ?v1 ?v2 ))(ite (fun_app$f ?v0 ?v1 )(sCons$ ?v1 (sfilter$ ?v0 ?v2 ))(sfilter$ ?v0 ?v2 ))):pattern ((sfilter$ ?v0 (sCons$ ?v1 ?v2 ))))):named a51 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_stream$ ))(! (= (sfilter$a ?v0 (sCons$a ?v1 ?v2 ))(ite (fun_app$g ?v0 ?v1 )(sCons$a ?v1 (sfilter$a ?v0 ?v2 ))(sfilter$a ?v0 ?v2 ))):pattern ((sfilter$a ?v0 (sCons$a ?v1 ?v2 ))))):named a52 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_stream$ ))(= (shd$a (smap$c ?v0 ?v1 ))(fun_app$c ?v0 (shd$a ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_stream$ ))(= (shd$a (smap$b ?v0 ?v1 ))(fun_app$b ?v0 (shd$ ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ ))(= (shd$ (smap$a ?v0 ?v1 ))(fun_app$a ?v0 (shd$ ?v1 )))):named a55 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_stream$ ))(= (shd$ (smap$ ?v0 ?v1 ))(fun_app$ ?v0 (shd$a ?v1 )))):named a56 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ )(?v3 Nat$ ))(= (snth$a (smap2$f ?v0 ?v1 ?v2 )?v3 )(fun_app$ (fun_app$n ?v0 (snth$ ?v1 ?v3 ))(snth$ ?v2 ?v3 )))):named a57 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ )(?v3 Nat$ ))(= (snth$ (smap2$e ?v0 ?v1 ?v2 )?v3 )(fun_app$b (fun_app$m ?v0 (snth$ ?v1 ?v3 ))(snth$a ?v2 ?v3 )))):named a58 ))
(assert (! (forall ((?v0 B_b_b_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ )(?v3 Nat$ ))(= (snth$ (smap2$g ?v0 ?v1 ?v2 )?v3 )(fun_app$c (fun_app$o ?v0 (snth$ ?v1 ?v3 ))(snth$ ?v2 ?v3 )))):named a59 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ )(?v3 Nat$ ))(= (snth$a (smap2$d ?v0 ?v1 ?v2 )?v3 )(fun_app$a (fun_app$l ?v0 (snth$ ?v1 ?v3 ))(snth$a ?v2 ?v3 )))):named a60 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ )(?v3 Nat$ ))(= (snth$ (smap2$c ?v0 ?v1 ?v2 )?v3 )(fun_app$c (fun_app$k ?v0 (snth$a ?v1 ?v3 ))(snth$ ?v2 ?v3 )))):named a61 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ )(?v3 Nat$ ))(= (snth$a (smap2$b ?v0 ?v1 ?v2 )?v3 )(fun_app$ (fun_app$j ?v0 (snth$a ?v1 ?v3 ))(snth$ ?v2 ?v3 )))):named a62 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ )(?v3 Nat$ ))(= (snth$ (smap2$a ?v0 ?v1 ?v2 )?v3 )(fun_app$b (fun_app$i ?v0 (snth$a ?v1 ?v3 ))(snth$a ?v2 ?v3 )))):named a63 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ )(?v3 Nat$ ))(= (snth$a (smap2$ ?v0 ?v1 ?v2 )?v3 )(fun_app$a (fun_app$h ?v0 (snth$a ?v1 ?v3 ))(snth$a ?v2 ?v3 )))):named a64 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_b_a_fun_fun$ )(?v2 B_stream$ )(?v3 B_stream$ ))(= (sdrop$a ?v0 (smap2$f ?v1 ?v2 ?v3 ))(smap2$f ?v1 (sdrop$ ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a65 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_a_b_fun_fun$ )(?v2 B_stream$ )(?v3 A_stream$ ))(= (sdrop$ ?v0 (smap2$e ?v1 ?v2 ?v3 ))(smap2$e ?v1 (sdrop$ ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a66 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_b_b_fun_fun$ )(?v2 B_stream$ )(?v3 B_stream$ ))(= (sdrop$ ?v0 (smap2$g ?v1 ?v2 ?v3 ))(smap2$g ?v1 (sdrop$ ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a67 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_a_a_fun_fun$ )(?v2 B_stream$ )(?v3 A_stream$ ))(= (sdrop$a ?v0 (smap2$d ?v1 ?v2 ?v3 ))(smap2$d ?v1 (sdrop$ ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a68 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_b_fun_fun$ )(?v2 A_stream$ )(?v3 B_stream$ ))(= (sdrop$ ?v0 (smap2$c ?v1 ?v2 ?v3 ))(smap2$c ?v1 (sdrop$a ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a69 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_b_a_fun_fun$ )(?v2 A_stream$ )(?v3 B_stream$ ))(= (sdrop$a ?v0 (smap2$b ?v1 ?v2 ?v3 ))(smap2$b ?v1 (sdrop$a ?v0 ?v2 )(sdrop$ ?v0 ?v3 )))):named a70 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_b_fun_fun$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (sdrop$ ?v0 (smap2$a ?v1 ?v2 ?v3 ))(smap2$a ?v1 (sdrop$a ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a71 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_a_fun_fun$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (sdrop$a ?v0 (smap2$ ?v1 ?v2 ?v3 ))(smap2$ ?v1 (sdrop$a ?v0 ?v2 )(sdrop$a ?v0 ?v3 )))):named a72 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ ))(= (shd$ (sdrop$a ?v0 ?v1 ))(snth$a ?v1 ?v0 ))):named a73 ))
(assert (! (forall ((?v0 Nat$ )(?v1 B_stream$ ))(= (shd$a (sdrop$ ?v0 ?v1 ))(snth$ ?v1 ?v0 ))):named a74 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ )(?v3 B_stream$ ))(= (= (smap2$e ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$b (fun_app$m ?v0 (snth$ ?v1 ?v4 ))(snth$a ?v2 ?v4 ))(snth$ ?v3 ?v4 ))))):named a75 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ )(?v3 A_stream$ ))(= (= (smap2$f ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$ (fun_app$n ?v0 (snth$ ?v1 ?v4 ))(snth$ ?v2 ?v4 ))(snth$a ?v3 ?v4 ))))):named a76 ))
(assert (! (forall ((?v0 B_b_b_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ )(?v3 B_stream$ ))(= (= (smap2$g ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$c (fun_app$o ?v0 (snth$ ?v1 ?v4 ))(snth$ ?v2 ?v4 ))(snth$ ?v3 ?v4 ))))):named a77 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (= (smap2$d ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$a (fun_app$l ?v0 (snth$ ?v1 ?v4 ))(snth$a ?v2 ?v4 ))(snth$a ?v3 ?v4 ))))):named a78 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ )(?v3 B_stream$ ))(= (= (smap2$c ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$c (fun_app$k ?v0 (snth$a ?v1 ?v4 ))(snth$ ?v2 ?v4 ))(snth$ ?v3 ?v4 ))))):named a79 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ )(?v3 A_stream$ ))(= (= (smap2$b ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$ (fun_app$j ?v0 (snth$a ?v1 ?v4 ))(snth$ ?v2 ?v4 ))(snth$a ?v3 ?v4 ))))):named a80 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ )(?v3 B_stream$ ))(= (= (smap2$a ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$b (fun_app$i ?v0 (snth$a ?v1 ?v4 ))(snth$a ?v2 ?v4 ))(snth$ ?v3 ?v4 ))))):named a81 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ )(?v3 A_stream$ ))(= (= (smap2$ ?v0 ?v1 ?v2 )?v3 )(forall ((?v4 Nat$ ))(= (fun_app$a (fun_app$h ?v0 (snth$a ?v1 ?v4 ))(snth$a ?v2 ?v4 ))(snth$a ?v3 ?v4 ))))):named a82 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (shd$ (smap2$ ?v0 ?v1 ?v2 ))(fun_app$a (fun_app$h ?v0 (shd$ ?v1 ))(shd$ ?v2 )))):named a83 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ ))(= (shd$ (smap2$b ?v0 ?v1 ?v2 ))(fun_app$ (fun_app$j ?v0 (shd$ ?v1 ))(shd$a ?v2 )))):named a84 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ ))(= (shd$ (smap2$d ?v0 ?v1 ?v2 ))(fun_app$a (fun_app$l ?v0 (shd$a ?v1 ))(shd$ ?v2 )))):named a85 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ ))(= (shd$ (smap2$f ?v0 ?v1 ?v2 ))(fun_app$ (fun_app$n ?v0 (shd$a ?v1 ))(shd$a ?v2 )))):named a86 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (shd$a (smap2$a ?v0 ?v1 ?v2 ))(fun_app$b (fun_app$i ?v0 (shd$ ?v1 ))(shd$ ?v2 )))):named a87 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ )(?v1 A_stream$ )(?v2 B_stream$ ))(= (shd$a (smap2$c ?v0 ?v1 ?v2 ))(fun_app$c (fun_app$k ?v0 (shd$ ?v1 ))(shd$a ?v2 )))):named a88 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B_stream$ )(?v2 A_stream$ ))(= (shd$a (smap2$e ?v0 ?v1 ?v2 ))(fun_app$b (fun_app$m ?v0 (shd$a ?v1 ))(shd$ ?v2 )))):named a89 ))
(assert (! (forall ((?v0 B_b_b_fun_fun$ )(?v1 B_stream$ )(?v2 B_stream$ ))(= (shd$a (smap2$g ?v0 ?v1 ?v2 ))(fun_app$c (fun_app$o ?v0 (shd$a ?v1 ))(shd$a ?v2 )))):named a90 ))
(assert (! (forall ((?v0 B_stream$ )(?v1 B_stream$ ))(= (shd$a (sinterleave$a ?v0 ?v1 ))(shd$a ?v0 ))):named a91 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(= (shd$ (sinterleave$ ?v0 ?v1 ))(shd$ ?v0 ))):named a92 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 Nat$ ))(member$ (snth$a ?v0 ?v1 )(sset$a ?v0 ))):named a93 ))
(assert (! (forall ((?v0 B_stream$ )(?v1 Nat$ ))(member$a (snth$ ?v0 ?v1 )(sset$ ?v0 ))):named a94 ))
(assert (! (forall ((?v0 A_stream$ ))(member$ (shd$ ?v0 )(sset$a ?v0 ))):named a95 ))
(assert (! (forall ((?v0 B_stream$ ))(member$a (shd$a ?v0 )(sset$ ?v0 ))):named a96 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (shd$ (sCons$ ?v0 ?v1 ))?v0 ):pattern ((sCons$ ?v0 ?v1 )))):named a97 ))
(assert (! (forall ((?v0 B$ )(?v1 B_stream$ ))(! (= (shd$a (sCons$a ?v0 ?v1 ))?v0 ):pattern ((sCons$a ?v0 ?v1 )))):named a98 ))
(check-sat )
;(get-unsat-core )
