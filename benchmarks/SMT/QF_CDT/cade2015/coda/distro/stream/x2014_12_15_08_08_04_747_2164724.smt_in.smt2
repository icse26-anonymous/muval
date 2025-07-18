;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-sort Nat_a_fun$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort Nat_nat_fun_nat_nat_fun_fun$ 0 )
(declare-codatatypes ()((A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))(Nat_stream$ (sCons$a (shd$a Nat$ )(stl$a Nat_stream$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun s$ ()A_stream$ )
(declare-fun uu$ ()Nat_a_fun$ )
(declare-fun suc$ ()Nat_nat_fun$ )
(declare-fun uua$ ()A_a_fun$ )
(declare-fun uub$ ()Nat_nat_fun$ )
(declare-fun smap$ (Nat_a_fun$ Nat_stream$ )A_stream$ )
(declare-fun snth$ (A_stream$ )Nat_a_fun$ )
(declare-fun minus$ (Nat$ )Nat_nat_fun$ )
(declare-fun smap$a (A_nat_fun$ A_stream$ )Nat_stream$ )
(declare-fun smap$b (Nat_nat_fun$ Nat_stream$ )Nat_stream$ )
(declare-fun smap$c (A_a_fun$ A_stream$ )A_stream$ )
(declare-fun snth$a (Nat_stream$ )Nat_nat_fun$ )
(declare-fun compow$ (Nat$ )A_a_fun_a_a_fun_fun$ )
(declare-fun compow$a (Nat$ )Nat_nat_fun_nat_nat_fun_fun$ )
(declare-fun fun_app$ (Nat_a_fun$ Nat$ )A$ )
(declare-fun fun_app$a (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun fun_app$b (A_a_fun$ A$ )A$ )
(declare-fun fun_app$c (A_nat_fun$ A$ )Nat$ )
(declare-fun fun_app$d (Nat_bool_fun$ Nat$ )Bool )
(declare-fun fun_app$e (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun fun_app$f (Nat_nat_fun_nat_nat_fun_fun$ Nat_nat_fun$ )Nat_nat_fun$ )
(declare-fun siterate$ (Nat_nat_fun$ Nat$ )Nat_stream$ )
(declare-fun siterate$a (A_a_fun$ A$ )A_stream$ )
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ uu$ ?v0 )(fun_app$ (snth$ s$ )(fun_app$a (minus$ ?v0 )n$ ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$a uub$ ?v0 )?v0 ):pattern ((fun_app$a uub$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b uua$ ?v0 )?v0 ):pattern ((fun_app$b uua$ ?v0 )))):named a2 ))
(assert (! (not (= s$ (smap$ uu$ (siterate$ suc$ n$ )))):named a3 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (fun_app$a (snth$a (smap$a ?v0 ?v1 ))?v2 )(fun_app$c ?v0 (fun_app$ (snth$ ?v1 )?v2 )))):named a4 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat_stream$ )(?v2 Nat$ ))(= (fun_app$a (snth$a (smap$b ?v0 ?v1 ))?v2 )(fun_app$a ?v0 (fun_app$a (snth$a ?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (fun_app$ (snth$ (smap$c ?v0 ?v1 ))?v2 )(fun_app$b ?v0 (fun_app$ (snth$ ?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 Nat_a_fun$ )(?v1 Nat_stream$ )(?v2 Nat$ ))(= (fun_app$ (snth$ (smap$ ?v0 ?v1 ))?v2 )(fun_app$ ?v0 (fun_app$a (snth$a ?v1 )?v2 )))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (smap$c ?v0 (siterate$a ?v0 ?v1 ))(siterate$a ?v0 (fun_app$b ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ ))(= (smap$b ?v0 (siterate$ ?v0 ?v1 ))(siterate$ ?v0 (fun_app$a ?v0 ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_nat_fun$ )(?v1 A_stream$ )(?v2 Nat_stream$ ))(= (= (smap$a ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$c ?v0 (fun_app$ (snth$ ?v1 )?v3 ))(fun_app$a (snth$a ?v2 )?v3 ))))):named a10 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat_stream$ )(?v2 Nat_stream$ ))(= (= (smap$b ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$a ?v0 (fun_app$a (snth$a ?v1 )?v3 ))(fun_app$a (snth$a ?v2 )?v3 ))))):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (= (smap$c ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$b ?v0 (fun_app$ (snth$ ?v1 )?v3 ))(fun_app$ (snth$ ?v2 )?v3 ))))):named a12 ))
(assert (! (forall ((?v0 Nat_a_fun$ )(?v1 Nat_stream$ )(?v2 A_stream$ ))(= (= (smap$ ?v0 ?v1 )?v2 )(forall ((?v3 Nat$ ))(= (fun_app$ ?v0 (fun_app$a (snth$a ?v1 )?v3 ))(fun_app$ (snth$ ?v2 )?v3 ))))):named a13 ))
(assert (! (forall ((?v0 A_stream$ ))(= (smap$c uua$ ?v0 )?v0 )):named a14 ))
(assert (! (forall ((?v0 Nat_stream$ ))(= (smap$b uub$ ?v0 )?v0 )):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$a (minus$ (fun_app$a (minus$ (fun_app$a suc$ ?v0 ))?v1 ))(fun_app$a suc$ ?v2 ))(fun_app$a (minus$ (fun_app$a (minus$ ?v0 )?v1 ))?v2 ))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (fun_app$a (minus$ (fun_app$a suc$ ?v0 ))(fun_app$a suc$ ?v1 ))(fun_app$a (minus$ ?v0 )?v1 )):pattern ((fun_app$a (minus$ (fun_app$a suc$ ?v0 ))(fun_app$a suc$ ?v1 ))))):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$a suc$ ?v0 )(fun_app$a suc$ ?v1 ))(= ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (fun_app$a suc$ ?v0 )(fun_app$a suc$ ?v1 ))(= ?v0 ?v1 ))):named a19 ))
(assert (! (forall ((?v0 Nat_bool_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (fun_app$d ?v0 ?v1 )(forall ((?v3 Nat$ ))(=> (fun_app$d ?v0 (fun_app$a suc$ ?v3 ))(fun_app$d ?v0 ?v3 ))))(fun_app$d ?v0 (fun_app$a (minus$ ?v1 )?v2 )))):named a20 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 Nat$ ))(= (fun_app$ (snth$ (siterate$a ?v0 ?v1 ))?v2 )(fun_app$b (fun_app$e (compow$ ?v2 )?v0 )?v1 ))):named a21 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$a (snth$a (siterate$ ?v0 ?v1 ))?v2 )(fun_app$a (fun_app$f (compow$a ?v2 )?v0 )?v1 ))):named a22 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$a (minus$ (fun_app$a (minus$ ?v0 )?v1 ))?v2 )(fun_app$a (minus$ (fun_app$a (minus$ ?v0 )?v2 ))?v1 ))):named a23 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= (fun_app$a suc$ ?v0 )(fun_app$a suc$ ?v1 ))(= ?v0 ?v1 ))):named a24 ))
(assert (! (forall ((?v0 Nat$ ))(not (= ?v0 (fun_app$a suc$ ?v0 )))):named a25 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$a (minus$ (fun_app$a (minus$ ?v0 )?v1 ))?v2 )(fun_app$a (minus$ (fun_app$a (minus$ ?v0 )?v2 ))?v1 ))):named a26 ))
(assert (! (forall ((?v0 Nat_nat_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$a ?v0 (fun_app$a (fun_app$f (compow$a ?v1 )?v0 )?v2 ))(fun_app$a (fun_app$f (compow$a ?v1 )?v0 )(fun_app$a ?v0 ?v2 )))):named a27 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 Nat$ )(?v2 A$ ))(= (fun_app$b ?v0 (fun_app$b (fun_app$e (compow$ ?v1 )?v0 )?v2 ))(fun_app$b (fun_app$e (compow$ ?v1 )?v0 )(fun_app$b ?v0 ?v2 )))):named a28 ))
(check-sat )
;(get-unsat-core )
