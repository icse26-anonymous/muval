;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_stream_set$ 0 )
(declare-sort A_a_stream_fun$ 0 )
(declare-sort A_stream_a_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_stream_stream_set$ 0 )
(declare-sort A_a_stream_stream_fun$ 0 )
(declare-sort A_stream_a_stream_fun$ 0 )
(declare-sort A_stream_stream_a_fun$ 0 )
(declare-sort A_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream_stream_bool_fun$ 0 )
(declare-sort A_stream_stream_stream_set$ 0 )
(declare-sort A_stream_a_stream_stream_fun$ 0 )
(declare-sort A_stream_stream_a_stream_fun$ 0 )
(declare-sort A_stream_stream_stream_bool_fun$ 0 )
(declare-sort A_stream_stream_stream_stream_set$ 0 )
(declare-sort A_stream_stream_a_stream_stream_fun$ 0 )
(declare-sort A_stream_a_stream_stream_bool_fun_fun$ 0 )
(declare-sort A_stream_stream_stream_stream_bool_fun$ 0 )
(declare-sort A_stream_stream_a_stream_stream_stream_bool_fun_fun$ 0 )
(declare-sort A_stream_stream_stream_a_stream_stream_stream_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-sort A_stream_stream$ 0)
(declare-sort A_stream_stream_stream$ 0)
(declare-sort A_stream_stream_stream_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun shd$a (A_stream_stream$)A_stream$)
(declare-fun stl$a (A_stream_stream$)A_stream_stream$)
(declare-fun sCons$a (A_stream$ A_stream_stream$ )A_stream_stream$)
(declare-fun shd$b (A_stream_stream_stream$)A_stream_stream$)
(declare-fun stl$b (A_stream_stream_stream$)A_stream_stream_stream$)
(declare-fun sCons$b (A_stream_stream$ A_stream_stream_stream$ )A_stream_stream_stream$)
(declare-fun shd$c (A_stream_stream_stream_stream$)A_stream_stream_stream$)
(declare-fun stl$c (A_stream_stream_stream_stream$)A_stream_stream_stream_stream$)
(declare-fun sCons$c (A_stream_stream_stream$ A_stream_stream_stream_stream$ )A_stream_stream_stream_stream$)
(declare-fun m$ ()Nat$ )
(declare-fun n$ ()Nat$ )
(declare-fun ss$ ()A_stream_stream$ )
(declare-fun smap$ (A_stream_stream_a_fun$ A_stream_stream_stream$ )A_stream$ )
(declare-fun snth$ (A_stream$ Nat$ )A$ )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun smap$a (A_stream_stream_a_stream_fun$ A_stream_stream_stream$ )A_stream_stream$ )
(declare-fun smap$b (A_a_stream_stream_fun$ A_stream$ )A_stream_stream_stream$ )
(declare-fun smap$c (A_stream_a_stream_stream_fun$ A_stream_stream$ )A_stream_stream_stream$ )
(declare-fun smap$d (A_stream_stream_a_stream_stream_fun$ A_stream_stream_stream$ )A_stream_stream_stream$ )
(declare-fun smap$e (A_a_fun$ )A_stream_a_stream_fun$ )
(declare-fun smap$f (A_stream_a_fun$ )A_stream_stream_a_stream_fun$ )
(declare-fun smap$g (A_a_stream_fun$ )A_stream_a_stream_stream_fun$ )
(declare-fun smap$h (A_stream_a_stream_fun$ )A_stream_stream_a_stream_stream_fun$ )
(declare-fun snth$a (A_stream_stream$ Nat$ )A_stream$ )
(declare-fun snth$b (A_stream_stream_stream_stream$ Nat$ )A_stream_stream_stream$ )
(declare-fun snth$c (A_stream_stream_stream$ Nat$ )A_stream_stream$ )
(declare-fun sset$a (A_stream_stream_stream_stream$ )A_stream_stream_stream_set$ )
(declare-fun sset$b (A_stream_stream_stream$ )A_stream_stream_set$ )
(declare-fun sset$c (A_stream_stream$ )A_stream_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun smerge$ (A_stream_stream$ )A_stream$ )
(declare-fun fun_app$ (A_stream_stream_bool_fun$ A_stream_stream$ )Bool )
(declare-fun member$a (A_stream_stream_stream$ A_stream_stream_stream_set$ )Bool )
(declare-fun member$b (A_stream_stream$ A_stream_stream_set$ )Bool )
(declare-fun member$c (A_stream$ A_stream_set$ )Bool )
(declare-fun member$d (A_stream_stream_stream_stream$ A_stream_stream_stream_stream_set$ )Bool )
(declare-fun smember$ (A_stream_stream_stream$ A_stream_stream_stream_stream$ )Bool )
(declare-fun streams$ (A_stream_stream_stream_set$ )A_stream_stream_stream_stream_set$ )
(declare-fun fun_app$a (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_stream_stream_a_fun$ A_stream_stream$ )A$ )
(declare-fun fun_app$d (A_stream_stream_a_stream_fun$ A_stream_stream$ )A_stream$ )
(declare-fun fun_app$e (A_a_stream_stream_fun$ A$ )A_stream_stream$ )
(declare-fun fun_app$f (A_stream_a_stream_stream_fun$ A_stream$ )A_stream_stream$ )
(declare-fun fun_app$g (A_stream_stream_a_stream_stream_fun$ A_stream_stream$ )A_stream_stream$ )
(declare-fun fun_app$h (A_stream_a_stream_fun$ A_stream$ )A_stream$ )
(declare-fun fun_app$i (A_a_fun$ A$ )A$ )
(declare-fun fun_app$j (A_stream_a_fun$ A_stream$ )A$ )
(declare-fun fun_app$k (A_a_stream_fun$ A$ )A_stream$ )
(declare-fun fun_app$l (A_stream_stream_stream_stream_bool_fun$ A_stream_stream_stream_stream$ )Bool )
(declare-fun fun_app$m (A_stream_stream_stream_a_stream_stream_stream_stream_bool_fun_fun$ A_stream_stream_stream$ )A_stream_stream_stream_stream_bool_fun$ )
(declare-fun fun_app$n (A_stream_stream_stream_bool_fun$ A_stream_stream_stream$ )Bool )
(declare-fun fun_app$o (A_stream_stream_a_stream_stream_stream_bool_fun_fun$ A_stream_stream$ )A_stream_stream_stream_bool_fun$ )
(declare-fun fun_app$p (A_stream_a_stream_stream_bool_fun_fun$ A_stream$ )A_stream_stream_bool_fun$ )
(declare-fun fun_app$q (A_a_stream_bool_fun_fun$ A$ )A_stream_bool_fun$ )
(declare-fun smember$a (A_stream_stream$ A_stream_stream_stream$ )Bool )
(declare-fun smember$b (A_stream$ )A_stream_stream_bool_fun$ )
(declare-fun smember$c (A$ )A_stream_bool_fun$ )
(declare-fun streams$a (A_stream_stream_set$ )A_stream_stream_stream_set$ )
(declare-fun streams$b (A_set$ )A_stream_set$ )
(declare-fun streams$c (A_stream_set$ )A_stream_stream_set$ )
(declare-fun stream_all$ (A_stream_stream_bool_fun$ A_stream_stream_stream$ )Bool )
(declare-fun stream_all$a (A_bool_fun$ )A_stream_bool_fun$ )
(declare-fun stream_all$b (A_stream_bool_fun$ )A_stream_stream_bool_fun$ )
(assert (! (not (member$ (snth$ (snth$a ss$ n$ )m$ )(sset$ (smerge$ ss$ )))):named a0 ))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$ )(?v1 Nat$ ))(member$a (snth$b ?v0 ?v1 )(sset$a ?v0 ))):named a1 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 Nat$ ))(member$b (snth$c ?v0 ?v1 )(sset$b ?v0 ))):named a2 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 Nat$ ))(member$c (snth$a ?v0 ?v1 )(sset$c ?v0 ))):named a3 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 Nat$ ))(member$ (snth$ ?v0 ?v1 )(sset$ ?v0 ))):named a4 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 A_stream_stream_stream_stream$ ))(! (= (smember$ ?v0 ?v1 )(member$a ?v0 (sset$a ?v1 ))):pattern ((smember$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream_stream$ ))(! (= (smember$a ?v0 ?v1 )(member$b ?v0 (sset$b ?v1 ))):pattern ((smember$a ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_stream$ ))(! (= (fun_app$ (smember$b ?v0 )?v1 )(member$c ?v0 (sset$c ?v1 ))):pattern ((fun_app$ (smember$b ?v0 )?v1 )))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (fun_app$a (smember$c ?v0 )?v1 )(member$ ?v0 (sset$ ?v1 ))):pattern ((fun_app$a (smember$c ?v0 )?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_stream_stream_bool_fun$ )(?v1 A_stream_stream_stream$ ))(= (stream_all$ ?v0 ?v1 )(forall ((?v2 Nat$ ))(fun_app$ ?v0 (snth$c ?v1 ?v2 ))))):named a9 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$a (stream_all$a ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$b ?v0 (snth$ ?v1 ?v2 ))))):named a10 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream_stream$ ))(= (fun_app$ (stream_all$b ?v0 )?v1 )(forall ((?v2 Nat$ ))(fun_app$a ?v0 (snth$a ?v1 ?v2 ))))):named a11 ))
(assert (! (forall ((?v0 A_stream_stream_a_fun$ )(?v1 A_stream_stream_stream$ )(?v2 Nat$ ))(= (snth$ (smap$ ?v0 ?v1 )?v2 )(fun_app$c ?v0 (snth$c ?v1 ?v2 )))):named a12 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$ )(?v1 A_stream_stream_stream$ )(?v2 Nat$ ))(= (snth$a (smap$a ?v0 ?v1 )?v2 )(fun_app$d ?v0 (snth$c ?v1 ?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_a_stream_stream_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$c (smap$b ?v0 ?v1 )?v2 )(fun_app$e ?v0 (snth$ ?v1 ?v2 )))):named a14 ))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$ )(?v1 A_stream_stream$ )(?v2 Nat$ ))(= (snth$c (smap$c ?v0 ?v1 )?v2 )(fun_app$f ?v0 (snth$a ?v1 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$ )(?v1 A_stream_stream_stream$ )(?v2 Nat$ ))(= (snth$c (smap$d ?v0 ?v1 )?v2 )(fun_app$g ?v0 (snth$c ?v1 ?v2 )))):named a16 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$ (fun_app$h (smap$e ?v0 )?v1 )?v2 )(fun_app$i ?v0 (snth$ ?v1 ?v2 )))):named a17 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream_stream$ )(?v2 Nat$ ))(= (snth$ (fun_app$d (smap$f ?v0 )?v1 )?v2 )(fun_app$j ?v0 (snth$a ?v1 ?v2 )))):named a18 ))
(assert (! (forall ((?v0 A_a_stream_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$a (fun_app$f (smap$g ?v0 )?v1 )?v2 )(fun_app$k ?v0 (snth$ ?v1 ?v2 )))):named a19 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_stream$ )(?v2 Nat$ ))(= (snth$a (fun_app$g (smap$h ?v0 )?v1 )?v2 )(fun_app$h ?v0 (snth$a ?v1 ?v2 )))):named a20 ))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$ )(?v1 A_stream_stream_stream_set$ ))(= (member$d ?v0 (streams$ ?v1 ))(forall ((?v2 Nat$ ))(member$a (snth$b ?v0 ?v2 )?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 A_stream_stream_set$ ))(= (member$a ?v0 (streams$a ?v1 ))(forall ((?v2 Nat$ ))(member$b (snth$c ?v0 ?v2 )?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_set$ ))(= (member$c ?v0 (streams$b ?v1 ))(forall ((?v2 Nat$ ))(member$ (snth$ ?v0 ?v2 )?v1 )))):named a23 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_set$ ))(= (member$b ?v0 (streams$c ?v1 ))(forall ((?v2 Nat$ ))(member$c (snth$a ?v0 ?v2 )?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$ )(?v1 A_stream_stream_stream_set$ )(?v2 Nat$ ))(=> (member$d ?v0 (streams$ ?v1 ))(member$a (snth$b ?v0 ?v2 )?v1 ))):named a25 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 A_stream_stream_set$ )(?v2 Nat$ ))(=> (member$a ?v0 (streams$a ?v1 ))(member$b (snth$c ?v0 ?v2 )?v1 ))):named a26 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_set$ )(?v2 Nat$ ))(=> (member$c ?v0 (streams$b ?v1 ))(member$ (snth$ ?v0 ?v2 )?v1 ))):named a27 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_set$ )(?v2 Nat$ ))(=> (member$b ?v0 (streams$c ?v1 ))(member$c (snth$a ?v0 ?v2 )?v1 ))):named a28 ))
(assert (! (forall ((?v0 A_a_stream_stream_fun$ )(?v1 A_stream$ )(?v2 A_stream_stream_stream$ ))(= (= (smap$b ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$e ?v0 (snth$ ?v1 ?v3 ))(snth$c ?v2 ?v3 ))))):named a29 ))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$ )(?v1 A_stream_stream$ )(?v2 A_stream_stream_stream$ ))(= (= (smap$c ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$f ?v0 (snth$a ?v1 ?v3 ))(snth$c ?v2 ?v3 ))))):named a30 ))
(assert (! (forall ((?v0 A_stream_stream_a_fun$ )(?v1 A_stream_stream_stream$ )(?v2 A_stream$ ))(= (= (smap$ ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$c ?v0 (snth$c ?v1 ?v3 ))(snth$ ?v2 ?v3 ))))):named a31 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$ )(?v1 A_stream_stream_stream$ )(?v2 A_stream_stream$ ))(= (= (smap$a ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$d ?v0 (snth$c ?v1 ?v3 ))(snth$a ?v2 ?v3 ))))):named a32 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$ )(?v1 A_stream_stream_stream$ )(?v2 A_stream_stream_stream$ ))(= (= (smap$d ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$g ?v0 (snth$c ?v1 ?v3 ))(snth$c ?v2 ?v3 ))))):named a33 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (= (fun_app$h (smap$e ?v0 )?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$i ?v0 (snth$ ?v1 ?v3 ))(snth$ ?v2 ?v3 ))))):named a34 ))
(assert (! (forall ((?v0 A_a_stream_fun$ )(?v1 A_stream$ )(?v2 A_stream_stream$ ))(= (= (fun_app$f (smap$g ?v0 )?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$k ?v0 (snth$ ?v1 ?v3 ))(snth$a ?v2 ?v3 ))))):named a35 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream_stream$ )(?v2 A_stream$ ))(= (= (fun_app$d (smap$f ?v0 )?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$j ?v0 (snth$a ?v1 ?v3 ))(snth$ ?v2 ?v3 ))))):named a36 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_stream$ )(?v2 A_stream_stream$ ))(= (= (fun_app$g (smap$h ?v0 )?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$h ?v0 (snth$a ?v1 ?v3 ))(snth$a ?v2 ?v3 ))))):named a37 ))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$ ))(member$a (shd$c ?v0 )(sset$a ?v0 ))):named a38 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ ))(member$b (shd$b ?v0 )(sset$b ?v0 ))):named a39 ))
(assert (! (forall ((?v0 A_stream_stream$ ))(member$c (shd$a ?v0 )(sset$c ?v0 ))):named a40 ))
(assert (! (forall ((?v0 A_stream$ ))(member$ (shd$ ?v0 )(sset$ ?v0 ))):named a41 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ )(?v2 A_a_stream_fun$ )(?v3 A_a_stream_fun$ ))(=> (and (forall ((?v4 A$ )(?v5 A$ ))(=> (and (member$ ?v4 (sset$ ?v0 ))(and (member$ ?v5 (sset$ ?v1 ))(= (fun_app$k ?v2 ?v4 )(fun_app$k ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (fun_app$f (smap$g ?v2 )?v0 )(fun_app$f (smap$g ?v3 )?v1 )))(= ?v0 ?v1 ))):named a42 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ ))(=> (and (forall ((?v4 A$ )(?v5 A$ ))(=> (and (member$ ?v4 (sset$ ?v0 ))(and (member$ ?v5 (sset$ ?v1 ))(= (fun_app$i ?v2 ?v4 )(fun_app$i ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (fun_app$h (smap$e ?v2 )?v0 )(fun_app$h (smap$e ?v3 )?v1 )))(= ?v0 ?v1 ))):named a43 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_a_stream_fun$ )(?v3 A_stream_a_stream_fun$ ))(=> (and (forall ((?v4 A_stream$ )(?v5 A_stream$ ))(=> (and (member$c ?v4 (sset$c ?v0 ))(and (member$c ?v5 (sset$c ?v1 ))(= (fun_app$h ?v2 ?v4 )(fun_app$h ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (fun_app$g (smap$h ?v2 )?v0 )(fun_app$g (smap$h ?v3 )?v1 )))(= ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_a_fun$ )(?v3 A_stream_a_fun$ ))(=> (and (forall ((?v4 A_stream$ )(?v5 A_stream$ ))(=> (and (member$c ?v4 (sset$c ?v0 ))(and (member$c ?v5 (sset$c ?v1 ))(= (fun_app$j ?v2 ?v4 )(fun_app$j ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (fun_app$d (smap$f ?v2 )?v0 )(fun_app$d (smap$f ?v3 )?v1 )))(= ?v0 ?v1 ))):named a45 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_a_stream_fun$ )(?v2 A_a_stream_fun$ ))(=> (forall ((?v3 A$ ))(=> (member$ ?v3 (sset$ ?v0 ))(= (fun_app$k ?v1 ?v3 )(fun_app$k ?v2 ?v3 ))))(= (fun_app$f (smap$g ?v1 )?v0 )(fun_app$f (smap$g ?v2 )?v0 )))):named a46 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ ))(=> (forall ((?v3 A$ ))(=> (member$ ?v3 (sset$ ?v0 ))(= (fun_app$i ?v1 ?v3 )(fun_app$i ?v2 ?v3 ))))(= (fun_app$h (smap$e ?v1 )?v0 )(fun_app$h (smap$e ?v2 )?v0 )))):named a47 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_a_stream_fun$ )(?v2 A_stream_a_stream_fun$ ))(=> (forall ((?v3 A_stream$ ))(=> (member$c ?v3 (sset$c ?v0 ))(= (fun_app$h ?v1 ?v3 )(fun_app$h ?v2 ?v3 ))))(= (fun_app$g (smap$h ?v1 )?v0 )(fun_app$g (smap$h ?v2 )?v0 )))):named a48 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_a_fun$ )(?v2 A_stream_a_fun$ ))(=> (forall ((?v3 A_stream$ ))(=> (member$c ?v3 (sset$c ?v0 ))(= (fun_app$j ?v1 ?v3 )(fun_app$j ?v2 ?v3 ))))(= (fun_app$d (smap$f ?v1 )?v0 )(fun_app$d (smap$f ?v2 )?v0 )))):named a49 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ )(?v2 A_a_stream_fun$ )(?v3 A_a_stream_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 (sset$ ?v1 ))(= (fun_app$k ?v2 ?v4 )(fun_app$k ?v3 ?v4 )))))(= (fun_app$f (smap$g ?v2 )?v0 )(fun_app$f (smap$g ?v3 )?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A$ ))(=> (member$ ?v4 (sset$ ?v1 ))(= (fun_app$i ?v2 ?v4 )(fun_app$i ?v3 ?v4 )))))(= (fun_app$h (smap$e ?v2 )?v0 )(fun_app$h (smap$e ?v3 )?v1 )))):named a51 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_a_stream_fun$ )(?v3 A_stream_a_stream_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A_stream$ ))(=> (member$c ?v4 (sset$c ?v1 ))(= (fun_app$h ?v2 ?v4 )(fun_app$h ?v3 ?v4 )))))(= (fun_app$g (smap$h ?v2 )?v0 )(fun_app$g (smap$h ?v3 )?v1 )))):named a52 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_a_fun$ )(?v3 A_stream_a_fun$ ))(=> (and (= ?v0 ?v1 )(forall ((?v4 A_stream$ ))(=> (member$c ?v4 (sset$c ?v1 ))(= (fun_app$j ?v2 ?v4 )(fun_app$j ?v3 ?v4 )))))(= (fun_app$d (smap$f ?v2 )?v0 )(fun_app$d (smap$f ?v3 )?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 A_stream_stream_stream_stream$ ))(=> (member$a ?v0 (sset$a (stl$c ?v1 )))(member$a ?v0 (sset$a ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream_stream$ ))(=> (member$b ?v0 (sset$b (stl$b ?v1 )))(member$b ?v0 (sset$b ?v1 )))):named a55 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_stream$ ))(=> (member$c ?v0 (sset$c (stl$a ?v1 )))(member$c ?v0 (sset$c ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(=> (member$ ?v0 (sset$ (stl$ ?v1 )))(member$ ?v0 (sset$ ?v1 )))):named a57 ))
(assert (! (forall ((?v0 A_stream_stream_stream$ )(?v1 A_stream_stream_stream_stream$ )(?v2 A_stream_stream_stream_a_stream_stream_stream_stream_bool_fun_fun$ ))(=> (and (member$a ?v0 (sset$a ?v1 ))(and (forall ((?v3 A_stream_stream_stream$ )(?v4 A_stream_stream_stream_stream$ ))(fun_app$l (fun_app$m ?v2 ?v3 )(sCons$c ?v3 ?v4 )))(forall ((?v3 A_stream_stream_stream$ )(?v4 A_stream_stream_stream_stream$ )(?v5 A_stream_stream_stream$ ))(=> (and (member$a ?v5 (sset$a ?v4 ))(fun_app$l (fun_app$m ?v2 ?v5 )?v4 ))(fun_app$l (fun_app$m ?v2 ?v5 )(sCons$c ?v3 ?v4 ))))))(fun_app$l (fun_app$m ?v2 ?v0 )?v1 ))):named a58 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream_stream$ )(?v2 A_stream_stream_a_stream_stream_stream_bool_fun_fun$ ))(=> (and (member$b ?v0 (sset$b ?v1 ))(and (forall ((?v3 A_stream_stream$ )(?v4 A_stream_stream_stream$ ))(fun_app$n (fun_app$o ?v2 ?v3 )(sCons$b ?v3 ?v4 )))(forall ((?v3 A_stream_stream$ )(?v4 A_stream_stream_stream$ )(?v5 A_stream_stream$ ))(=> (and (member$b ?v5 (sset$b ?v4 ))(fun_app$n (fun_app$o ?v2 ?v5 )?v4 ))(fun_app$n (fun_app$o ?v2 ?v5 )(sCons$b ?v3 ?v4 ))))))(fun_app$n (fun_app$o ?v2 ?v0 )?v1 ))):named a59 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_a_stream_stream_bool_fun_fun$ ))(=> (and (member$c ?v0 (sset$c ?v1 ))(and (forall ((?v3 A_stream$ )(?v4 A_stream_stream$ ))(fun_app$ (fun_app$p ?v2 ?v3 )(sCons$a ?v3 ?v4 )))(forall ((?v3 A_stream$ )(?v4 A_stream_stream$ )(?v5 A_stream$ ))(=> (and (member$c ?v5 (sset$c ?v4 ))(fun_app$ (fun_app$p ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$p ?v2 ?v5 )(sCons$a ?v3 ?v4 ))))))(fun_app$ (fun_app$p ?v2 ?v0 )?v1 ))):named a60 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A_a_stream_bool_fun_fun$ ))(=> (and (member$ ?v0 (sset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_stream$ ))(fun_app$a (fun_app$q ?v2 ?v3 )(sCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_stream$ )(?v5 A$ ))(=> (and (member$ ?v5 (sset$ ?v4 ))(fun_app$a (fun_app$q ?v2 ?v5 )?v4 ))(fun_app$a (fun_app$q ?v2 ?v5 )(sCons$ ?v3 ?v4 ))))))(fun_app$a (fun_app$q ?v2 ?v0 )?v1 ))):named a61 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream$ )(?v3 A_stream_stream$ ))(= (= (sCons$a ?v0 ?v1 )(sCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a62 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream_stream$ )(?v2 A_stream_stream$ )(?v3 A_stream_stream_stream$ ))(= (= (sCons$b ?v0 ?v1 )(sCons$b ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a63 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ )(?v3 A_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a64 ))
(assert (! (forall ((?v0 A_stream_stream_a_fun$ )(?v1 A_stream_stream_stream$ ))(= (stl$ (smap$ ?v0 ?v1 ))(smap$ ?v0 (stl$b ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$ )(?v1 A_stream_stream_stream$ ))(= (stl$a (smap$a ?v0 ?v1 ))(smap$a ?v0 (stl$b ?v1 )))):named a66 ))
(assert (! (forall ((?v0 A_a_stream_stream_fun$ )(?v1 A_stream$ ))(= (stl$b (smap$b ?v0 ?v1 ))(smap$b ?v0 (stl$ ?v1 )))):named a67 ))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$ )(?v1 A_stream_stream$ ))(= (stl$b (smap$c ?v0 ?v1 ))(smap$c ?v0 (stl$a ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$ )(?v1 A_stream_stream_stream$ ))(= (stl$b (smap$d ?v0 ?v1 ))(smap$d ?v0 (stl$b ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_stream$ ))(= (stl$a (fun_app$g (smap$h ?v0 )?v1 ))(fun_app$g (smap$h ?v0 )(stl$a ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_a_stream_fun$ )(?v1 A_stream$ ))(= (stl$a (fun_app$f (smap$g ?v0 )?v1 ))(fun_app$f (smap$g ?v0 )(stl$ ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream_stream$ ))(= (stl$ (fun_app$d (smap$f ?v0 )?v1 ))(fun_app$d (smap$f ?v0 )(stl$a ?v1 )))):named a72 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ ))(= (stl$ (fun_app$h (smap$e ?v0 )?v1 ))(fun_app$h (smap$e ?v0 )(stl$ ?v1 )))):named a73 ))
(assert (! (forall ((?v0 A_stream_stream_a_fun$ )(?v1 A_stream_stream_stream$ ))(= (shd$ (smap$ ?v0 ?v1 ))(fun_app$c ?v0 (shd$b ?v1 )))):named a74 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$ )(?v1 A_stream_stream_stream$ ))(= (shd$a (smap$a ?v0 ?v1 ))(fun_app$d ?v0 (shd$b ?v1 )))):named a75 ))
(assert (! (forall ((?v0 A_a_stream_stream_fun$ )(?v1 A_stream$ ))(= (shd$b (smap$b ?v0 ?v1 ))(fun_app$e ?v0 (shd$ ?v1 )))):named a76 ))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$ )(?v1 A_stream_stream$ ))(= (shd$b (smap$c ?v0 ?v1 ))(fun_app$f ?v0 (shd$a ?v1 )))):named a77 ))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$ )(?v1 A_stream_stream_stream$ ))(= (shd$b (smap$d ?v0 ?v1 ))(fun_app$g ?v0 (shd$b ?v1 )))):named a78 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_stream$ ))(= (shd$a (fun_app$g (smap$h ?v0 )?v1 ))(fun_app$h ?v0 (shd$a ?v1 )))):named a79 ))
(assert (! (forall ((?v0 A_a_stream_fun$ )(?v1 A_stream$ ))(= (shd$a (fun_app$f (smap$g ?v0 )?v1 ))(fun_app$k ?v0 (shd$ ?v1 )))):named a80 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream_stream$ ))(= (shd$ (fun_app$d (smap$f ?v0 )?v1 ))(fun_app$j ?v0 (shd$a ?v1 )))):named a81 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ ))(= (shd$ (fun_app$h (smap$e ?v0 )?v1 ))(fun_app$i ?v0 (shd$ ?v1 )))):named a82 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ )(?v2 A_stream_stream$ ))(! (= (fun_app$ (smember$b ?v0 )(sCons$a ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (fun_app$ (smember$b ?v0 )?v2 ))):pattern ((fun_app$ (smember$b ?v0 )(sCons$a ?v1 ?v2 ))))):named a83 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream$ )(?v2 A_stream_stream_stream$ ))(! (= (smember$a ?v0 (sCons$b ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (smember$a ?v0 ?v2 ))):pattern ((smember$a ?v0 (sCons$b ?v1 ?v2 ))))):named a84 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_stream$ ))(! (= (fun_app$a (smember$c ?v0 )(sCons$ ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (fun_app$a (smember$c ?v0 )?v2 ))):pattern ((fun_app$a (smember$c ?v0 )(sCons$ ?v1 ?v2 ))))):named a85 ))
(check-sat )
;(get-unsat-core )
