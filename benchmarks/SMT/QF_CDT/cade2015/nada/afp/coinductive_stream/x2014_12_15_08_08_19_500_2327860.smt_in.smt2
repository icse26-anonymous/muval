;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort A_stream_set$ 0 )
(declare-sort A_a_stream_fun$ 0 )
(declare-sort A_stream_a_fun$ 0 )
(declare-sort A_nat_a_fun_fun$ 0 )
(declare-sort Nat_a_stream_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort A_stream_stream_set$ 0 )
(declare-sort A_stream_a_stream_fun$ 0 )
(declare-sort A_stream_stream_bool_fun$ 0 )
(declare-sort A_stream_stream_stream_set$ 0 )
(declare-sort A_stream_stream_a_stream_stream_fun$ 0 )
(declare-sort A_stream_bool_fun_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ 0 )
(declare-sort A_stream_stream_bool_fun_a_stream_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-sort A_stream_stream$ 0)
(declare-sort A_stream_stream_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun shd$a (A_stream_stream$)A_stream$)
(declare-fun stl$a (A_stream_stream$)A_stream_stream$)
(declare-fun sCons$a (A_stream$ A_stream_stream$ )A_stream_stream$)
(declare-fun shd$b (A_stream_stream_stream$)A_stream_stream$)
(declare-fun stl$b (A_stream_stream_stream$)A_stream_stream_stream$)
(declare-fun sCons$b (A_stream_stream$ A_stream_stream_stream$ )A_stream_stream_stream$)
(declare-fun a$ ()A$ )
(declare-fun ev$ (A_stream_stream_bool_fun$ )A_stream_stream_bool_fun$ )
(declare-fun id$ ()A_a_fun$ )
(declare-fun uu$ ()Nat_a_fun$ )
(declare-fun alw$ (A_stream_stream_bool_fun$ )A_stream_stream_bool_fun$ )
(declare-fun ev$a (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun id$a ()A_stream_a_stream_fun$ )
(declare-fun id$b ()A_stream_stream_a_stream_stream_fun$ )
(declare-fun uua$ (A_stream_a_stream_fun$ A_stream$ )Nat_a_stream_fun$ )
(declare-fun uub$ (A_a_fun$ )A_nat_a_fun_fun$ )
(declare-fun uuc$ ()A_a_fun$ )
(declare-fun alw$a (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun smap$ (A_a_stream_fun$ A_stream$ )A_stream_stream$ )
(declare-fun snth$ (A_stream$ )Nat_a_fun$ )
(declare-fun smap$a (A_stream_a_fun$ A_stream_stream$ )A_stream$ )
(declare-fun smap$b (A_stream_a_stream_fun$ A_stream_stream$ )A_stream_stream$ )
(declare-fun smap$c (A_a_fun$ )A_stream_a_stream_fun$ )
(declare-fun compow$ (Nat$ )A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ )
(declare-fun member$ (A_stream_stream$ A_stream_stream_set$ )Bool )
(declare-fun of_seq$ (Nat_a_fun$ )A_stream$ )
(declare-fun suntil$ (A_stream_stream_bool_fun$ )A_stream_stream_bool_fun_a_stream_stream_bool_fun_fun$ )
(declare-fun compow$a (Nat$ )A_a_fun_a_a_fun_fun$ )
(declare-fun fun_app$ (Nat_a_stream_fun$ Nat$ )A_stream$ )
(declare-fun member$a (A_stream_stream_stream$ A_stream_stream_stream_set$ )Bool )
(declare-fun member$b (A_stream$ A_stream_set$ )Bool )
(declare-fun member$c (A$ A_set$ )Bool )
(declare-fun of_seq$a (Nat_a_stream_fun$ )A_stream_stream$ )
(declare-fun streams$ (A_stream_stream_set$ )A_stream_stream_stream_set$ )
(declare-fun suntil$a (A_stream_bool_fun$ )A_stream_bool_fun_a_stream_bool_fun_fun$ )
(declare-fun fun_app$a (A_stream_a_stream_fun$ A_stream$ )A_stream$ )
(declare-fun fun_app$b (A_stream_a_stream_fun_a_stream_a_stream_fun_fun$ A_stream_a_stream_fun$ )A_stream_a_stream_fun$ )
(declare-fun fun_app$c (Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$d (A_nat_a_fun_fun$ A$ )Nat_a_fun$ )
(declare-fun fun_app$e (A_a_fun$ A$ )A$ )
(declare-fun fun_app$f (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun fun_app$g (A_a_stream_fun$ A$ )A_stream$ )
(declare-fun fun_app$h (A_stream_stream_bool_fun$ A_stream_stream$ )Bool )
(declare-fun fun_app$i (A_stream_stream_bool_fun_a_stream_stream_bool_fun_fun$ A_stream_stream_bool_fun$ )A_stream_stream_bool_fun$ )
(declare-fun fun_app$j (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$k (A_stream_bool_fun_a_stream_bool_fun_fun$ A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun fun_app$l (A_stream_a_fun$ A_stream$ )A$ )
(declare-fun siterate$ (A_a_fun$ )A_a_stream_fun$ )
(declare-fun streams$a (A_stream_set$ )A_stream_stream_set$ )
(declare-fun streams$b (A_set$ )A_stream_set$ )
(declare-fun siterate$a (A_stream_a_stream_fun$ A_stream$ )A_stream_stream$ )
(declare-fun siterate$b (A_stream_stream_a_stream_stream_fun$ A_stream_stream$ )A_stream_stream_stream$ )
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(! (= (fun_app$ (uua$ ?v0 ?v1 )?v2 )(fun_app$a (fun_app$b (compow$ ?v2 )?v0 )?v1 )):pattern ((fun_app$ (uua$ ?v0 ?v1 )?v2 )))):named a0 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 Nat$ ))(! (= (fun_app$c (fun_app$d (uub$ ?v0 )?v1 )?v2 )(fun_app$e (fun_app$f (compow$a ?v2 )?v0 )?v1 )):pattern ((fun_app$c (fun_app$d (uub$ ?v0 )?v1 )?v2 )))):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$e uuc$ ?v0 )?v0 ):pattern ((fun_app$e uuc$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$c uu$ ?v0 )a$ ):pattern ((fun_app$c uu$ ?v0 )))):named a3 ))
(assert (! (not (= (fun_app$g (siterate$ id$ )a$ )(of_seq$ uu$ ))):named a4 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$a id$a ?v0 )?v0 ):pattern ((fun_app$a id$a ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$e id$ ?v0 )?v0 ):pattern ((fun_app$e id$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$a id$a ?v0 )?v0 ):pattern ((fun_app$a id$a ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$e id$ ?v0 )?v0 ):pattern ((fun_app$e id$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream$ ))(= (siterate$a ?v0 ?v1 )(of_seq$a (uua$ ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (fun_app$g (siterate$ ?v0 )?v1 )(of_seq$ (fun_app$d (uub$ ?v0 )?v1 )))):named a10 ))
(assert (! (forall ((?v0 Nat_a_fun$ ))(= (snth$ (of_seq$ ?v0 ))?v0 )):named a11 ))
(assert (! (forall ((?v0 A_stream$ ))(= (of_seq$ (snth$ ?v0 ))?v0 )):named a12 ))
(assert (! (forall ((?v0 A_stream_stream_bool_fun$ )(?v1 A_stream_stream_bool_fun$ )(?v2 A_stream$ ))(= (fun_app$h (fun_app$i (suntil$ ?v0 )?v1 )(siterate$a id$a ?v2 ))(fun_app$h ?v1 (siterate$a id$a ?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream_bool_fun$ )(?v2 A$ ))(= (fun_app$j (fun_app$k (suntil$a ?v0 )?v1 )(fun_app$g (siterate$ id$ )?v2 ))(fun_app$j ?v1 (fun_app$g (siterate$ id$ )?v2 )))):named a14 ))
(assert (! (forall ((?v0 A_stream_stream$ )(?v1 A_stream_stream_set$ ))(=> (member$ ?v0 ?v1 )(member$a (siterate$b id$b ?v0 )(streams$ ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_set$ ))(=> (member$b ?v0 ?v1 )(member$ (siterate$a id$a ?v0 )(streams$a ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ ))(=> (member$c ?v0 ?v1 )(member$b (fun_app$g (siterate$ id$ )?v0 )(streams$b ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_a_stream_fun$ )(?v1 A$ ))(= (smap$ ?v0 (fun_app$g (siterate$ id$ )?v1 ))(siterate$a id$a (fun_app$g ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_stream_a_fun$ )(?v1 A_stream$ ))(= (smap$a ?v0 (siterate$a id$a ?v1 ))(fun_app$g (siterate$ id$ )(fun_app$l ?v0 ?v1 )))):named a19 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream$ ))(= (smap$b ?v0 (siterate$a id$a ?v1 ))(siterate$a id$a (fun_app$a ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (fun_app$a (smap$c ?v0 )(fun_app$g (siterate$ id$ )?v1 ))(fun_app$g (siterate$ id$ )(fun_app$e ?v0 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_stream_stream_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$h (alw$ ?v0 )(siterate$a id$a ?v1 ))(fun_app$h ?v0 (siterate$a id$a ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A$ ))(= (fun_app$j (alw$a ?v0 )(fun_app$g (siterate$ id$ )?v1 ))(fun_app$j ?v0 (fun_app$g (siterate$ id$ )?v1 )))):named a23 ))
(assert (! (forall ((?v0 A_stream_stream_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$h (ev$ ?v0 )(siterate$a id$a ?v1 ))(fun_app$h ?v0 (siterate$a id$a ?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A$ ))(= (fun_app$j (ev$a ?v0 )(fun_app$g (siterate$ id$ )?v1 ))(fun_app$j ?v0 (fun_app$g (siterate$ id$ )?v1 )))):named a25 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream$ ))(= (smap$b ?v0 (siterate$a ?v0 ?v1 ))(siterate$a ?v0 (fun_app$a ?v0 ?v1 )))):named a26 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (fun_app$a (smap$c ?v0 )(fun_app$g (siterate$ ?v0 )?v1 ))(fun_app$g (siterate$ ?v0 )(fun_app$e ?v0 ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream$ ))(= (siterate$a ?v0 ?v1 )(sCons$a ?v1 (siterate$a ?v0 (fun_app$a ?v0 ?v1 ))))):named a28 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (fun_app$g (siterate$ ?v0 )?v1 )(sCons$ ?v1 (fun_app$g (siterate$ ?v0 )(fun_app$e ?v0 ?v1 ))))):named a29 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ ))(= (ev$a (ev$a ?v0 ))(ev$a ?v0 ))):named a30 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A$ )(?v3 A_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a31 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ ))(= (alw$a (alw$a ?v0 ))(alw$a ?v0 ))):named a32 ))
(assert (! (forall ((?v0 A_stream$ ))(= (fun_app$a (smap$c uuc$ )?v0 )?v0 )):named a33 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (fun_app$c (snth$ (fun_app$a (smap$c ?v0 )?v1 ))?v2 )(fun_app$e ?v0 (fun_app$c (snth$ ?v1 )?v2 )))):named a34 ))
(check-sat )
;(get-unsat-core )
