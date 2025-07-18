;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_list_set$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_list_list_bool_fun$ 0 )
(declare-sort A_list_stream_bool_fun$ 0 )
(declare-sort A_list_list_list_bool_fun$ 0 )
(declare-sort A_list_list_stream_bool_fun$ 0 )
(declare-sort A_stream_a_stream_bool_fun_fun$ 0 )
(declare-sort A_list_list_list_stream_bool_fun$ 0 )
(declare-sort A_list_stream_a_list_stream_bool_fun_fun$ 0 )
(declare-sort A_list_list_stream_a_list_list_stream_bool_fun_fun$ 0 )
(declare-sort A_list_list_list_stream_a_list_list_list_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-sort A_list_stream$ 0)
(declare-fun shd$a (A_list_stream$)A_list$)
(declare-fun stl$a (A_list_stream$)A_list_stream$)
(declare-fun sCons$a (A_list$ A_list_stream$ )A_list_stream$)
(declare-datatypes ()((A_list_list$ (nil$a )(cons$a (hd$a A_list$ )(tl$a A_list_list$ )))(A_list_list_list$ (nil$b )(cons$b (hd$b A_list_list$ )(tl$b A_list_list_list$ )))))
(declare-sort A_list_list_list_stream$ 0)
(declare-sort A_list_list_stream$ 0)
(declare-fun shd$b (A_list_list_list_stream$)A_list_list_list$)
(declare-fun stl$b (A_list_list_list_stream$)A_list_list_list_stream$)
(declare-fun sCons$b (A_list_list_list$ A_list_list_list_stream$ )A_list_list_list_stream$)
(declare-fun shd$c (A_list_list_stream$)A_list_list$)
(declare-fun stl$c (A_list_list_stream$)A_list_list_stream$)
(declare-fun sCons$c (A_list_list$ A_list_list_stream$ )A_list_list_stream$)
(declare-datatypes ()((A_list_list_list_list$ (nil$c )(cons$c (hd$c A_list_list_list$ )(tl$c A_list_list_list_list$ )))))
(declare-sort A_list_list_list_list_stream$ 0)
(declare-fun shd$d (A_list_list_list_list_stream$)A_list_list_list_list$)
(declare-fun stl$d (A_list_list_list_list_stream$)A_list_list_list_list_stream$)
(declare-fun sCons$d (A_list_list_list_list$ A_list_list_list_list_stream$ )A_list_list_list_list_stream$)
(declare-fun m$ ()Nat$ )
(declare-fun s$ ()A_list_stream$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()Nat$ )
(declare-fun sa$ ()A_list_stream$ )
(declare-fun flat$ (A_list_stream$ )A_stream$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun size$ (A_list$ )Nat$ )
(declare-fun snth$ (A_stream$ Nat$ )A$ )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun flat$a (A_list_list_list_list_stream$ )A_list_list_list_stream$ )
(declare-fun flat$b (A_list_list_list_stream$ )A_list_list_stream$ )
(declare-fun flat$c (A_list_list_stream$ )A_list_stream$ )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun sdrop$ (Nat$ A_list_list_list_stream$ )A_list_list_list_stream$ )
(declare-fun snth$a (A_list_list_list_stream$ Nat$ )A_list_list_list$ )
(declare-fun snth$b (A_list_list_stream$ Nat$ )A_list_list$ )
(declare-fun snth$c (A_list_stream$ Nat$ )A_list$ )
(declare-fun sset$a (A_list_stream$ )A_list_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun sdrop$a (Nat$ A_list_list_stream$ )A_list_list_stream$ )
(declare-fun sdrop$b (Nat$ A_stream$ )A_stream$ )
(declare-fun sdrop$c (Nat$ A_list_stream$ )A_list_stream$ )
(declare-fun fun_app$ (A_list_list_list_stream_bool_fun$ A_list_list_list_stream$ )Bool )
(declare-fun member$a (A_list$ A_list_set$ )Bool )
(declare-fun fun_app$a (A_list_list_list_stream_a_list_list_list_stream_bool_fun_fun$ A_list_list_list_stream$ )A_list_list_list_stream_bool_fun$ )
(declare-fun fun_app$b (A_list_list_stream_bool_fun$ A_list_list_stream$ )Bool )
(declare-fun fun_app$c (A_list_list_stream_a_list_list_stream_bool_fun_fun$ A_list_list_stream$ )A_list_list_stream_bool_fun$ )
(declare-fun fun_app$d (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$e (A_stream_a_stream_bool_fun_fun$ A_stream$ )A_stream_bool_fun$ )
(declare-fun fun_app$f (A_list_stream_bool_fun$ A_list_stream$ )Bool )
(declare-fun fun_app$g (A_list_stream_a_list_stream_bool_fun_fun$ A_list_stream$ )A_list_stream_bool_fun$ )
(declare-fun fun_app$h (A_list_list_list_bool_fun$ A_list_list_list$ )Bool )
(declare-fun fun_app$i (A_list_list_bool_fun$ A_list_list$ )Bool )
(declare-fun fun_app$j (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$k (A_list_bool_fun$ A_list$ )Bool )
(declare-fun sdrop_while$ (A_list_list_list_bool_fun$ A_list_list_list_stream$ )A_list_list_list_stream$ )
(declare-fun sdrop_while$a (A_list_list_bool_fun$ A_list_list_stream$ )A_list_list_stream$ )
(declare-fun sdrop_while$b (A_bool_fun$ A_stream$ )A_stream$ )
(declare-fun sdrop_while$c (A_list_bool_fun$ A_list_stream$ )A_list_stream$ )
(assert (! (not (= x$ (snth$ (flat$ (stl$a sa$ ))(minus$ y$ (size$ (shd$a sa$ )))))):named a0 ))
(assert (! (not (less$ y$ (size$ (shd$a sa$ )))):named a1 ))
(assert (! (= x$ (snth$ (flat$ sa$ )y$ )):named a2 ))
(assert (! (= x$ (snth$ (flat$ s$ )m$ )):named a3 ))
(assert (! (=> (forall ((?v0 Nat$ ))(=> (= x$ (snth$ (flat$ s$ )?v0 ))false ))false ):named a4 ))
(assert (! (forall ((?v0 A_list_list_list_stream$ )(?v1 A_list_list_list_stream$ ))(=> (and (= (shd$b ?v0 )(shd$b ?v1 ))(= (stl$b ?v0 )(stl$b ?v1 )))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_list_list_stream$ )(?v1 A_list_list_stream$ ))(=> (and (= (shd$c ?v0 )(shd$c ?v1 ))(= (stl$c ?v0 )(stl$c ?v1 )))(= ?v0 ?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(=> (and (= (shd$ ?v0 )(shd$ ?v1 ))(= (stl$ ?v0 )(stl$ ?v1 )))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_list_stream$ )(?v1 A_list_stream$ ))(=> (and (= (shd$a ?v0 )(shd$a ?v1 ))(= (stl$a ?v0 )(stl$a ?v1 )))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_list_list_list_stream_a_list_list_list_stream_bool_fun_fun$ )(?v1 A_list_list_list_stream$ )(?v2 A_list_list_list_stream$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(forall ((?v3 A_list_list_list_stream$ )(?v4 A_list_list_list_stream$ ))(=> (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(and (= (shd$b ?v3 )(shd$b ?v4 ))(or (fun_app$ (fun_app$a ?v0 (stl$b ?v3 ))(stl$b ?v4 ))(= (stl$b ?v3 )(stl$b ?v4 )))))))(= ?v1 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 A_list_list_stream_a_list_list_stream_bool_fun_fun$ )(?v1 A_list_list_stream$ )(?v2 A_list_list_stream$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_list_list_stream$ )(?v4 A_list_list_stream$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (shd$c ?v3 )(shd$c ?v4 ))(or (fun_app$b (fun_app$c ?v0 (stl$c ?v3 ))(stl$c ?v4 ))(= (stl$c ?v3 )(stl$c ?v4 )))))))(= ?v1 ?v2 ))):named a10 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$d (fun_app$e ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(or (fun_app$d (fun_app$e ?v0 (stl$ ?v3 ))(stl$ ?v4 ))(= (stl$ ?v3 )(stl$ ?v4 )))))))(= ?v1 ?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_list_stream_a_list_stream_bool_fun_fun$ )(?v1 A_list_stream$ )(?v2 A_list_stream$ ))(=> (and (fun_app$f (fun_app$g ?v0 ?v1 )?v2 )(forall ((?v3 A_list_stream$ )(?v4 A_list_stream$ ))(=> (fun_app$f (fun_app$g ?v0 ?v3 )?v4 )(and (= (shd$a ?v3 )(shd$a ?v4 ))(or (fun_app$f (fun_app$g ?v0 (stl$a ?v3 ))(stl$a ?v4 ))(= (stl$a ?v3 )(stl$a ?v4 )))))))(= ?v1 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_list_list_list_stream_a_list_list_list_stream_bool_fun_fun$ )(?v1 A_list_list_list_stream$ )(?v2 A_list_list_list_stream$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(forall ((?v3 A_list_list_list_stream$ )(?v4 A_list_list_list_stream$ ))(=> (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(and (= (shd$b ?v3 )(shd$b ?v4 ))(fun_app$ (fun_app$a ?v0 (stl$b ?v3 ))(stl$b ?v4 ))))))(= ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 A_list_list_stream_a_list_list_stream_bool_fun_fun$ )(?v1 A_list_list_stream$ )(?v2 A_list_list_stream$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_list_list_stream$ )(?v4 A_list_list_stream$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (shd$c ?v3 )(shd$c ?v4 ))(fun_app$b (fun_app$c ?v0 (stl$c ?v3 ))(stl$c ?v4 ))))))(= ?v1 ?v2 ))):named a14 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$d (fun_app$e ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(fun_app$d (fun_app$e ?v0 (stl$ ?v3 ))(stl$ ?v4 ))))))(= ?v1 ?v2 ))):named a15 ))
(assert (! (forall ((?v0 A_list_stream_a_list_stream_bool_fun_fun$ )(?v1 A_list_stream$ )(?v2 A_list_stream$ ))(=> (and (fun_app$f (fun_app$g ?v0 ?v1 )?v2 )(forall ((?v3 A_list_stream$ )(?v4 A_list_stream$ ))(=> (fun_app$f (fun_app$g ?v0 ?v3 )?v4 )(and (= (shd$a ?v3 )(shd$a ?v4 ))(fun_app$f (fun_app$g ?v0 (stl$a ?v3 ))(stl$a ?v4 ))))))(= ?v1 ?v2 ))):named a16 ))
(assert (! (member$ x$ (sset$ (flat$ s$ ))):named a17 ))
(assert (! (forall ((?v0 A_list_list_list_list_stream$ ))(= (shd$b (flat$a ?v0 ))(hd$c (shd$d ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_list_list_list_stream$ ))(= (shd$c (flat$b ?v0 ))(hd$b (shd$b ?v0 )))):named a19 ))
(assert (! (forall ((?v0 A_list_stream$ ))(= (shd$ (flat$ ?v0 ))(hd$ (shd$a ?v0 )))):named a20 ))
(assert (! (forall ((?v0 A_list_list_stream$ ))(= (shd$a (flat$c ?v0 ))(hd$a (shd$c ?v0 )))):named a21 ))
(assert (! (forall ((?v0 A_list$ ))(=> (member$a ?v0 (sset$a sa$ ))(not (= ?v0 nil$ )))):named a22 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list_list_list_stream$ ))(= (shd$b (sdrop$ ?v0 ?v1 ))(snth$a ?v1 ?v0 ))):named a23 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list_list_stream$ ))(= (shd$c (sdrop$a ?v0 ?v1 ))(snth$b ?v1 ?v0 ))):named a24 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_stream$ ))(= (shd$ (sdrop$b ?v0 ?v1 ))(snth$ ?v1 ?v0 ))):named a25 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list_stream$ ))(= (shd$a (sdrop$c ?v0 ?v1 ))(snth$c ?v1 ?v0 ))):named a26 ))
(assert (! (forall ((?v0 A_list_list_list_bool_fun$ )(?v1 A_list_list_list_stream$ ))(= (sdrop_while$ ?v0 ?v1 )(ite (fun_app$h ?v0 (shd$b ?v1 ))(sdrop_while$ ?v0 (stl$b ?v1 ))?v1 ))):named a27 ))
(assert (! (forall ((?v0 A_list_list_bool_fun$ )(?v1 A_list_list_stream$ ))(= (sdrop_while$a ?v0 ?v1 )(ite (fun_app$i ?v0 (shd$c ?v1 ))(sdrop_while$a ?v0 (stl$c ?v1 ))?v1 ))):named a28 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_stream$ ))(= (sdrop_while$b ?v0 ?v1 )(ite (fun_app$j ?v0 (shd$ ?v1 ))(sdrop_while$b ?v0 (stl$ ?v1 ))?v1 ))):named a29 ))
(assert (! (forall ((?v0 A_list_bool_fun$ )(?v1 A_list_stream$ ))(= (sdrop_while$c ?v0 ?v1 )(ite (fun_app$k ?v0 (shd$a ?v1 ))(sdrop_while$c ?v0 (stl$a ?v1 ))?v1 ))):named a30 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a31 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (not (= (size$ ?v0 )(size$ ?v1 )))(= (= ?v0 ?v1 )false ))):named a32 ))
(assert (! (forall ((?v0 Nat$ ))(exists ((?v1 A_list$ ))(= (size$ ?v1 )?v0 ))):named a33 ))
(check-sat )
;(get-unsat-core )
