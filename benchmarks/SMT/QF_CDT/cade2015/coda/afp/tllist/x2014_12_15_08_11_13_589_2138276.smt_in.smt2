;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort A_a_tllist_bool_fun$ 0 )
(declare-sort A_b_tllist_bool_fun$ 0 )
(declare-sort B_a_tllist_bool_fun$ 0 )
(declare-sort B_b_tllist_bool_fun$ 0 )
(declare-sort A_a_a_tllist_bool_fun_fun$ 0 )
(declare-sort A_a_b_tllist_bool_fun_fun$ 0 )
(declare-sort B_b_a_tllist_bool_fun_fun$ 0 )
(declare-sort B_b_b_tllist_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))(A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))(B_b_tllist$ (tNil$a (terminal$a B$ ))(tCons$a (thd$a B$ )(ttl$a B_b_tllist$ )))(B_a_tllist$ (tNil$b (terminal$b A$ ))(tCons$b (thd$b B$ )(ttl$b B_a_tllist$ )))(A_a_tllist$ (tNil$c (terminal$c A$ ))(tCons$c (thd$c A$ )(ttl$c A_a_tllist$ )))))
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun lset$ (A_llist$ )A_set$ )
(declare-fun tmap$ (A_a_fun$ B_b_fun$ A_b_tllist$ )A_b_tllist$ )
(declare-fun tset$ (A_b_tllist$ )A_set$ )
(declare-fun tmap$a (A_a_fun$ A_b_fun$ A_a_tllist$ )A_b_tllist$ )
(declare-fun tmap$b (A_a_fun$ B_a_fun$ A_b_tllist$ )A_a_tllist$ )
(declare-fun tmap$c (A_a_fun$ A_a_fun$ A_a_tllist$ )A_a_tllist$ )
(declare-fun tset$a (B_b_tllist$ )B_set$ )
(declare-fun tset$b (B_a_tllist$ )B_set$ )
(declare-fun tset$c (A_a_tllist$ )A_set$ )
(declare-fun insert$ (B$ B_set$ )B_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (B_b_tllist_bool_fun$ B_b_tllist$ )Bool )
(declare-fun insert$a (A$ A_set$ )A_set$ )
(declare-fun is_TNil$ (B_b_tllist$ )Bool )
(declare-fun less_eq$ (B_set$ B_set$ )Bool )
(declare-fun member$a (B$ B_set$ )Bool )
(declare-fun fun_app$a (B_b_b_tllist_bool_fun_fun$ B$ )B_b_tllist_bool_fun$ )
(declare-fun fun_app$b (B_a_tllist_bool_fun$ B_a_tllist$ )Bool )
(declare-fun fun_app$c (B_b_a_tllist_bool_fun_fun$ B$ )B_a_tllist_bool_fun$ )
(declare-fun fun_app$d (A_a_tllist_bool_fun$ A_a_tllist$ )Bool )
(declare-fun fun_app$e (A_a_a_tllist_bool_fun_fun$ A$ )A_a_tllist_bool_fun$ )
(declare-fun fun_app$f (A_b_tllist_bool_fun$ A_b_tllist$ )Bool )
(declare-fun fun_app$g (A_a_b_tllist_bool_fun_fun$ A$ )A_b_tllist_bool_fun$ )
(declare-fun fun_app$h (A_a_fun$ A$ )A$ )
(declare-fun fun_app$i (B_b_fun$ B$ )B$ )
(declare-fun fun_app$j (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$l (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$m (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$n (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun fun_app$o (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun is_TNil$a (B_a_tllist$ )Bool )
(declare-fun is_TNil$b (A_a_tllist$ )Bool )
(declare-fun is_TNil$c (A_b_tllist$ )Bool )
(declare-fun less_eq$a (A_set$ A_set$ )Bool )
(declare-fun set2_tllist$ (A_b_tllist$ )B_set$ )
(declare-fun tllist_all2$ (A_a_bool_fun_fun$ A_a_bool_fun_fun$ A_a_tllist$ A_a_tllist$ )Bool )
(declare-fun set2_tllist$a (A_a_tllist$ )A_set$ )
(declare-fun set2_tllist$b (B_a_tllist$ )A_set$ )
(declare-fun set2_tllist$c (B_b_tllist$ )B_set$ )
(declare-fun tllist_all2$a (A_a_bool_fun_fun$ A_b_bool_fun_fun$ A_a_tllist$ A_b_tllist$ )Bool )
(declare-fun tllist_all2$b (A_a_bool_fun_fun$ B_a_bool_fun_fun$ A_b_tllist$ A_a_tllist$ )Bool )
(declare-fun tllist_all2$c (A_a_bool_fun_fun$ B_b_bool_fun_fun$ A_b_tllist$ A_b_tllist$ )Bool )
(declare-fun tllist_all2$d (B_b_bool_fun_fun$ A_a_bool_fun_fun$ B_a_tllist$ B_a_tllist$ )Bool )
(declare-fun tllist_all2$e (B_b_bool_fun_fun$ A_b_bool_fun_fun$ B_a_tllist$ B_b_tllist$ )Bool )
(declare-fun tllist_all2$f (B_b_bool_fun_fun$ B_a_bool_fun_fun$ B_b_tllist$ B_a_tllist$ )Bool )
(declare-fun tllist_all2$g (B_b_bool_fun_fun$ B_b_bool_fun_fun$ B_b_tllist$ B_b_tllist$ )Bool )
(declare-fun tllist_all2$h (B_a_bool_fun_fun$ A_b_bool_fun_fun$ B_a_tllist$ A_b_tllist$ )Bool )
(declare-fun tllist_all2$i (B_a_bool_fun_fun$ B_b_bool_fun_fun$ B_b_tllist$ A_b_tllist$ )Bool )
(declare-fun tllist_all2$j (B_a_bool_fun_fun$ A_a_bool_fun_fun$ B_a_tllist$ A_a_tllist$ )Bool )
(declare-fun tllist_all2$k (A_b_bool_fun_fun$ B_b_bool_fun_fun$ A_b_tllist$ B_b_tllist$ )Bool )
(declare-fun tllist_all2$l (A_b_bool_fun_fun$ B_a_bool_fun_fun$ A_b_tllist$ B_a_tllist$ )Bool )
(declare-fun tllist_all2$m (A_b_bool_fun_fun$ A_b_bool_fun_fun$ A_a_tllist$ B_b_tllist$ )Bool )
(declare-fun tllist_all2$n (A_b_bool_fun_fun$ A_a_bool_fun_fun$ A_a_tllist$ B_a_tllist$ )Bool )
(declare-fun llist_of_tllist$ (A_b_tllist$ )A_llist$ )
(assert (! (not (member$ x$ (tset$ xs$ ))):named a0 ))
(assert (! (member$ x$ (lset$ (llist_of_tllist$ xs$ ))):named a1 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ ))(=> (member$a ?v0 (tset$a (ttl$a ?v1 )))(member$a ?v0 (tset$a ?v1 )))):named a2 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ ))(=> (member$a ?v0 (tset$b (ttl$b ?v1 )))(member$a ?v0 (tset$b ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ ))(=> (member$ ?v0 (tset$c (ttl$c ?v1 )))(member$ ?v0 (tset$c ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(=> (member$ ?v0 (tset$ (ttl$ ?v1 )))(member$ ?v0 (tset$ ?v1 )))):named a5 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ )(?v2 B_b_b_tllist_bool_fun_fun$ ))(=> (and (member$a ?v0 (tset$a ?v1 ))(and (forall ((?v3 B$ )(?v4 B_b_tllist$ ))(fun_app$ (fun_app$a ?v2 ?v3 )(tCons$a ?v3 ?v4 )))(forall ((?v3 B$ )(?v4 B_b_tllist$ )(?v5 B$ ))(=> (and (member$a ?v5 (tset$a ?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )?v4 ))(fun_app$ (fun_app$a ?v2 ?v5 )(tCons$a ?v3 ?v4 ))))))(fun_app$ (fun_app$a ?v2 ?v0 )?v1 ))):named a6 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ )(?v2 B_b_a_tllist_bool_fun_fun$ ))(=> (and (member$a ?v0 (tset$b ?v1 ))(and (forall ((?v3 B$ )(?v4 B_a_tllist$ ))(fun_app$b (fun_app$c ?v2 ?v3 )(tCons$b ?v3 ?v4 )))(forall ((?v3 B$ )(?v4 B_a_tllist$ )(?v5 B$ ))(=> (and (member$a ?v5 (tset$b ?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )?v4 ))(fun_app$b (fun_app$c ?v2 ?v5 )(tCons$b ?v3 ?v4 ))))))(fun_app$b (fun_app$c ?v2 ?v0 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ )(?v2 A_a_a_tllist_bool_fun_fun$ ))(=> (and (member$ ?v0 (tset$c ?v1 ))(and (forall ((?v3 A$ )(?v4 A_a_tllist$ ))(fun_app$d (fun_app$e ?v2 ?v3 )(tCons$c ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_a_tllist$ )(?v5 A$ ))(=> (and (member$ ?v5 (tset$c ?v4 ))(fun_app$d (fun_app$e ?v2 ?v5 )?v4 ))(fun_app$d (fun_app$e ?v2 ?v5 )(tCons$c ?v3 ?v4 ))))))(fun_app$d (fun_app$e ?v2 ?v0 )?v1 ))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A_a_b_tllist_bool_fun_fun$ ))(=> (and (member$ ?v0 (tset$ ?v1 ))(and (forall ((?v3 A$ )(?v4 A_b_tllist$ ))(fun_app$f (fun_app$g ?v2 ?v3 )(tCons$ ?v3 ?v4 )))(forall ((?v3 A$ )(?v4 A_b_tllist$ )(?v5 A$ ))(=> (and (member$ ?v5 (tset$ ?v4 ))(fun_app$f (fun_app$g ?v2 ?v5 )?v4 ))(fun_app$f (fun_app$g ?v2 ?v5 )(tCons$ ?v3 ?v4 ))))))(fun_app$f (fun_app$g ?v2 ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ ))(=> (and (member$a ?v0 (tset$a ?v1 ))(and (forall ((?v2 B_b_tllist$ ))(=> (= ?v1 (tCons$a ?v0 ?v2 ))false ))(forall ((?v2 B$ )(?v3 B_b_tllist$ ))(=> (and (= ?v1 (tCons$a ?v2 ?v3 ))(member$a ?v0 (tset$a ?v3 )))false ))))false )):named a10 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ ))(=> (and (member$a ?v0 (tset$b ?v1 ))(and (forall ((?v2 B_a_tllist$ ))(=> (= ?v1 (tCons$b ?v0 ?v2 ))false ))(forall ((?v2 B$ )(?v3 B_a_tllist$ ))(=> (and (= ?v1 (tCons$b ?v2 ?v3 ))(member$a ?v0 (tset$b ?v3 )))false ))))false )):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ ))(=> (and (member$ ?v0 (tset$c ?v1 ))(and (forall ((?v2 A_a_tllist$ ))(=> (= ?v1 (tCons$c ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_a_tllist$ ))(=> (and (= ?v1 (tCons$c ?v2 ?v3 ))(member$ ?v0 (tset$c ?v3 )))false ))))false )):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(=> (and (member$ ?v0 (tset$ ?v1 ))(and (forall ((?v2 A_b_tllist$ ))(=> (= ?v1 (tCons$ ?v0 ?v2 ))false ))(forall ((?v2 A$ )(?v3 A_b_tllist$ ))(=> (and (= ?v1 (tCons$ ?v2 ?v3 ))(member$ ?v0 (tset$ ?v3 )))false ))))false )):named a13 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ )(?v2 B$ ))(=> (member$a ?v0 (tset$a ?v1 ))(member$a ?v0 (tset$a (tCons$a ?v2 ?v1 ))))):named a14 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ )(?v2 B$ ))(=> (member$a ?v0 (tset$b ?v1 ))(member$a ?v0 (tset$b (tCons$b ?v2 ?v1 ))))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ )(?v2 A$ ))(=> (member$ ?v0 (tset$c ?v1 ))(member$ ?v0 (tset$c (tCons$c ?v2 ?v1 ))))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ ))(=> (member$ ?v0 (tset$ ?v1 ))(member$ ?v0 (tset$ (tCons$ ?v2 ?v1 ))))):named a17 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ ))(member$a ?v0 (tset$a (tCons$a ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ ))(member$a ?v0 (tset$b (tCons$b ?v0 ?v1 )))):named a19 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ ))(member$ ?v0 (tset$c (tCons$c ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(member$ ?v0 (tset$ (tCons$ ?v0 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_b_tllist$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ )(?v4 B_b_fun$ )(?v5 B_b_fun$ ))(=> (and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$ ?v0 ))(and (member$ ?v7 (tset$ ?v1 ))(= (fun_app$h ?v2 ?v6 )(fun_app$h ?v3 ?v7 ))))(= ?v6 ?v7 )))(and (forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (set2_tllist$ ?v0 ))(and (member$a ?v7 (set2_tllist$ ?v1 ))(= (fun_app$i ?v4 ?v6 )(fun_app$i ?v5 ?v7 ))))(= ?v6 ?v7 )))(= (tmap$ ?v2 ?v4 ?v0 )(tmap$ ?v3 ?v5 ?v1 ))))(= ?v0 ?v1 ))):named a22 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ )(?v3 B_b_fun$ )(?v4 B_b_fun$ ))(=> (and (forall ((?v5 A$ ))(=> (member$ ?v5 (tset$ ?v0 ))(= (fun_app$h ?v1 ?v5 )(fun_app$h ?v2 ?v5 ))))(forall ((?v5 B$ ))(=> (member$a ?v5 (set2_tllist$ ?v0 ))(= (fun_app$i ?v3 ?v5 )(fun_app$i ?v4 ?v5 )))))(= (tmap$ ?v1 ?v3 ?v0 )(tmap$ ?v2 ?v4 ?v0 )))):named a23 ))
(assert (! (forall ((?v0 A_b_tllist$ )(?v1 A_b_tllist$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ )(?v4 B_b_fun$ )(?v5 B_b_fun$ ))(=> (and (= ?v0 ?v1 )(and (forall ((?v6 A$ ))(=> (member$ ?v6 (tset$ ?v1 ))(= (fun_app$h ?v2 ?v6 )(fun_app$h ?v3 ?v6 ))))(forall ((?v6 B$ ))(=> (member$a ?v6 (set2_tllist$ ?v1 ))(= (fun_app$i ?v4 ?v6 )(fun_app$i ?v5 ?v6 ))))))(= (tmap$ ?v2 ?v4 ?v0 )(tmap$ ?v3 ?v5 ?v1 )))):named a24 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_tllist$ ))(! (= (tset$a (tCons$a ?v0 ?v1 ))(insert$ ?v0 (tset$a ?v1 ))):pattern ((tCons$a ?v0 ?v1 )))):named a25 ))
(assert (! (forall ((?v0 B$ )(?v1 B_a_tllist$ ))(! (= (tset$b (tCons$b ?v0 ?v1 ))(insert$ ?v0 (tset$b ?v1 ))):pattern ((tCons$b ?v0 ?v1 )))):named a26 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ ))(! (= (tset$c (tCons$c ?v0 ?v1 ))(insert$a ?v0 (tset$c ?v1 ))):pattern ((tCons$c ?v0 ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ ))(! (= (tset$ (tCons$ ?v0 ?v1 ))(insert$a ?v0 (tset$ ?v1 ))):pattern ((tCons$ ?v0 ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 A_a_tllist$ )(?v3 A_a_tllist$ )(?v4 A_a_bool_fun_fun$ )(?v5 A_a_bool_fun_fun$ ))(=> (and (tllist_all2$ ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$c ?v2 ))(and (member$ ?v7 (tset$c ?v3 ))(fun_app$j (fun_app$k ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v4 ?v6 )?v7 )))(forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (set2_tllist$a ?v2 ))(and (member$ ?v7 (set2_tllist$a ?v3 ))(fun_app$j (fun_app$k ?v1 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v5 ?v6 )?v7 )))))(tllist_all2$ ?v4 ?v5 ?v2 ?v3 ))):named a29 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_b_bool_fun_fun$ )(?v2 A_a_tllist$ )(?v3 A_b_tllist$ )(?v4 A_a_bool_fun_fun$ )(?v5 A_b_bool_fun_fun$ ))(=> (and (tllist_all2$a ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$c ?v2 ))(and (member$ ?v7 (tset$ ?v3 ))(fun_app$j (fun_app$k ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v4 ?v6 )?v7 )))(forall ((?v6 A$ )(?v7 B$ ))(=> (and (member$ ?v6 (set2_tllist$a ?v2 ))(and (member$a ?v7 (set2_tllist$ ?v3 ))(fun_app$l (fun_app$m ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$m ?v5 ?v6 )?v7 )))))(tllist_all2$a ?v4 ?v5 ?v2 ?v3 ))):named a30 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_a_bool_fun_fun$ )(?v2 A_b_tllist$ )(?v3 A_a_tllist$ )(?v4 A_a_bool_fun_fun$ )(?v5 B_a_bool_fun_fun$ ))(=> (and (tllist_all2$b ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$ ?v2 ))(and (member$ ?v7 (tset$c ?v3 ))(fun_app$j (fun_app$k ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v4 ?v6 )?v7 )))(forall ((?v6 B$ )(?v7 A$ ))(=> (and (member$a ?v6 (set2_tllist$ ?v2 ))(and (member$ ?v7 (set2_tllist$a ?v3 ))(fun_app$j (fun_app$n ?v1 ?v6 )?v7 )))(fun_app$j (fun_app$n ?v5 ?v6 )?v7 )))))(tllist_all2$b ?v4 ?v5 ?v2 ?v3 ))):named a31 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A_b_tllist$ )(?v3 A_b_tllist$ )(?v4 A_a_bool_fun_fun$ )(?v5 B_b_bool_fun_fun$ ))(=> (and (tllist_all2$c ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (tset$ ?v2 ))(and (member$ ?v7 (tset$ ?v3 ))(fun_app$j (fun_app$k ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v4 ?v6 )?v7 )))(forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (set2_tllist$ ?v2 ))(and (member$a ?v7 (set2_tllist$ ?v3 ))(fun_app$l (fun_app$o ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v5 ?v6 )?v7 )))))(tllist_all2$c ?v4 ?v5 ?v2 ?v3 ))):named a32 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 B_a_tllist$ )(?v3 B_a_tllist$ )(?v4 B_b_bool_fun_fun$ )(?v5 A_a_bool_fun_fun$ ))(=> (and (tllist_all2$d ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (tset$b ?v2 ))(and (member$a ?v7 (tset$b ?v3 ))(fun_app$l (fun_app$o ?v0 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v4 ?v6 )?v7 )))(forall ((?v6 A$ )(?v7 A$ ))(=> (and (member$ ?v6 (set2_tllist$b ?v2 ))(and (member$ ?v7 (set2_tllist$b ?v3 ))(fun_app$j (fun_app$k ?v1 ?v6 )?v7 )))(fun_app$j (fun_app$k ?v5 ?v6 )?v7 )))))(tllist_all2$d ?v4 ?v5 ?v2 ?v3 ))):named a33 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 A_b_bool_fun_fun$ )(?v2 B_a_tllist$ )(?v3 B_b_tllist$ )(?v4 B_b_bool_fun_fun$ )(?v5 A_b_bool_fun_fun$ ))(=> (and (tllist_all2$e ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (tset$b ?v2 ))(and (member$a ?v7 (tset$a ?v3 ))(fun_app$l (fun_app$o ?v0 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v4 ?v6 )?v7 )))(forall ((?v6 A$ )(?v7 B$ ))(=> (and (member$ ?v6 (set2_tllist$b ?v2 ))(and (member$a ?v7 (set2_tllist$c ?v3 ))(fun_app$l (fun_app$m ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$m ?v5 ?v6 )?v7 )))))(tllist_all2$e ?v4 ?v5 ?v2 ?v3 ))):named a34 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_a_bool_fun_fun$ )(?v2 B_b_tllist$ )(?v3 B_a_tllist$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_a_bool_fun_fun$ ))(=> (and (tllist_all2$f ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (tset$a ?v2 ))(and (member$a ?v7 (tset$b ?v3 ))(fun_app$l (fun_app$o ?v0 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v4 ?v6 )?v7 )))(forall ((?v6 B$ )(?v7 A$ ))(=> (and (member$a ?v6 (set2_tllist$c ?v2 ))(and (member$ ?v7 (set2_tllist$b ?v3 ))(fun_app$j (fun_app$n ?v1 ?v6 )?v7 )))(fun_app$j (fun_app$n ?v5 ?v6 )?v7 )))))(tllist_all2$f ?v4 ?v5 ?v2 ?v3 ))):named a35 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_b_tllist$ )(?v3 B_b_tllist$ )(?v4 B_b_bool_fun_fun$ )(?v5 B_b_bool_fun_fun$ ))(=> (and (tllist_all2$g ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (tset$a ?v2 ))(and (member$a ?v7 (tset$a ?v3 ))(fun_app$l (fun_app$o ?v0 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v4 ?v6 )?v7 )))(forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (set2_tllist$c ?v2 ))(and (member$a ?v7 (set2_tllist$c ?v3 ))(fun_app$l (fun_app$o ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v5 ?v6 )?v7 )))))(tllist_all2$g ?v4 ?v5 ?v2 ?v3 ))):named a36 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 A_b_bool_fun_fun$ )(?v2 B_a_tllist$ )(?v3 A_b_tllist$ )(?v4 B_a_bool_fun_fun$ )(?v5 A_b_bool_fun_fun$ ))(=> (and (tllist_all2$h ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 A$ ))(=> (and (member$a ?v6 (tset$b ?v2 ))(and (member$ ?v7 (tset$ ?v3 ))(fun_app$j (fun_app$n ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$n ?v4 ?v6 )?v7 )))(forall ((?v6 A$ )(?v7 B$ ))(=> (and (member$ ?v6 (set2_tllist$b ?v2 ))(and (member$a ?v7 (set2_tllist$ ?v3 ))(fun_app$l (fun_app$m ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$m ?v5 ?v6 )?v7 )))))(tllist_all2$h ?v4 ?v5 ?v2 ?v3 ))):named a37 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 B_b_tllist$ )(?v3 A_b_tllist$ )(?v4 B_a_bool_fun_fun$ )(?v5 B_b_bool_fun_fun$ ))(=> (and (tllist_all2$i ?v0 ?v1 ?v2 ?v3 )(and (forall ((?v6 B$ )(?v7 A$ ))(=> (and (member$a ?v6 (tset$a ?v2 ))(and (member$ ?v7 (tset$ ?v3 ))(fun_app$j (fun_app$n ?v0 ?v6 )?v7 )))(fun_app$j (fun_app$n ?v4 ?v6 )?v7 )))(forall ((?v6 B$ )(?v7 B$ ))(=> (and (member$a ?v6 (set2_tllist$c ?v2 ))(and (member$a ?v7 (set2_tllist$ ?v3 ))(fun_app$l (fun_app$o ?v1 ?v6 )?v7 )))(fun_app$l (fun_app$o ?v5 ?v6 )?v7 )))))(tllist_all2$i ?v4 ?v5 ?v2 ?v3 ))):named a38 ))
(assert (! (forall ((?v0 B_b_tllist$ ))(=> (not (is_TNil$ ?v0 ))(member$a (thd$a ?v0 )(tset$a ?v0 )))):named a39 ))
(assert (! (forall ((?v0 B_a_tllist$ ))(=> (not (is_TNil$a ?v0 ))(member$a (thd$b ?v0 )(tset$b ?v0 )))):named a40 ))
(assert (! (forall ((?v0 A_a_tllist$ ))(=> (not (is_TNil$b ?v0 ))(member$ (thd$c ?v0 )(tset$c ?v0 )))):named a41 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(=> (not (is_TNil$c ?v0 ))(member$ (thd$ ?v0 )(tset$ ?v0 )))):named a42 ))
(assert (! (forall ((?v0 B_b_tllist$ ))(less_eq$ (tset$a (ttl$a ?v0 ))(tset$a ?v0 ))):named a43 ))
(assert (! (forall ((?v0 B_a_tllist$ ))(less_eq$ (tset$b (ttl$b ?v0 ))(tset$b ?v0 ))):named a44 ))
(assert (! (forall ((?v0 A_a_tllist$ ))(less_eq$a (tset$c (ttl$c ?v0 ))(tset$c ?v0 ))):named a45 ))
(assert (! (forall ((?v0 A_b_tllist$ ))(less_eq$a (tset$ (ttl$ ?v0 ))(tset$ ?v0 ))):named a46 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_tllist$ )(?v2 A$ )(?v3 A_a_tllist$ ))(= (= (tCons$c ?v0 ?v1 )(tCons$c ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a47 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_tllist$ )(?v2 A$ )(?v3 A_b_tllist$ ))(= (= (tCons$ ?v0 ?v1 )(tCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a48 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_b_fun$ )(?v2 A_a_tllist$ ))(= (is_TNil$c (tmap$a ?v0 ?v1 ?v2 ))(is_TNil$b ?v2 ))):named a49 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_a_fun$ )(?v2 A_b_tllist$ ))(= (is_TNil$b (tmap$b ?v0 ?v1 ?v2 ))(is_TNil$c ?v2 ))):named a50 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun$ )(?v2 A_a_tllist$ ))(= (is_TNil$b (tmap$c ?v0 ?v1 ?v2 ))(is_TNil$b ?v2 ))):named a51 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_tllist$ ))(= (is_TNil$c (tmap$ ?v0 ?v1 ?v2 ))(is_TNil$c ?v2 ))):named a52 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 B$ )(?v3 B_a_tllist$ )(?v4 A$ )(?v5 A_a_tllist$ ))(! (= (tllist_all2$j ?v0 ?v1 (tCons$b ?v2 ?v3 )(tCons$c ?v4 ?v5 ))(and (fun_app$j (fun_app$n ?v0 ?v2 )?v4 )(tllist_all2$j ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$j ?v0 ?v1 (tCons$b ?v2 ?v3 )(tCons$c ?v4 ?v5 ))))):named a53 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A$ )(?v3 A_b_tllist$ )(?v4 B$ )(?v5 B_b_tllist$ ))(! (= (tllist_all2$k ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$a ?v4 ?v5 ))(and (fun_app$l (fun_app$m ?v0 ?v2 )?v4 )(tllist_all2$k ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$k ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$a ?v4 ?v5 ))))):named a54 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 B_a_bool_fun_fun$ )(?v2 A$ )(?v3 A_b_tllist$ )(?v4 B$ )(?v5 B_a_tllist$ ))(! (= (tllist_all2$l ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$b ?v4 ?v5 ))(and (fun_app$l (fun_app$m ?v0 ?v2 )?v4 )(tllist_all2$l ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$l ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$b ?v4 ?v5 ))))):named a55 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_b_bool_fun_fun$ )(?v2 A$ )(?v3 A_a_tllist$ )(?v4 B$ )(?v5 B_b_tllist$ ))(! (= (tllist_all2$m ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$a ?v4 ?v5 ))(and (fun_app$l (fun_app$m ?v0 ?v2 )?v4 )(tllist_all2$m ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$m ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$a ?v4 ?v5 ))))):named a56 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 A$ )(?v3 A_a_tllist$ )(?v4 B$ )(?v5 B_a_tllist$ ))(! (= (tllist_all2$n ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$b ?v4 ?v5 ))(and (fun_app$l (fun_app$m ?v0 ?v2 )?v4 )(tllist_all2$n ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$n ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$b ?v4 ?v5 ))))):named a57 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_b_bool_fun_fun$ )(?v2 A$ )(?v3 A_b_tllist$ )(?v4 A$ )(?v5 A_b_tllist$ ))(! (= (tllist_all2$c ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$ ?v4 ?v5 ))(and (fun_app$j (fun_app$k ?v0 ?v2 )?v4 )(tllist_all2$c ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$c ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$ ?v4 ?v5 ))))):named a58 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 B_a_bool_fun_fun$ )(?v2 A$ )(?v3 A_b_tllist$ )(?v4 A$ )(?v5 A_a_tllist$ ))(! (= (tllist_all2$b ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$c ?v4 ?v5 ))(and (fun_app$j (fun_app$k ?v0 ?v2 )?v4 )(tllist_all2$b ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$b ?v0 ?v1 (tCons$ ?v2 ?v3 )(tCons$c ?v4 ?v5 ))))):named a59 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_b_bool_fun_fun$ )(?v2 A$ )(?v3 A_a_tllist$ )(?v4 A$ )(?v5 A_b_tllist$ ))(! (= (tllist_all2$a ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$ ?v4 ?v5 ))(and (fun_app$j (fun_app$k ?v0 ?v2 )?v4 )(tllist_all2$a ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$a ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$ ?v4 ?v5 ))))):named a60 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_a_bool_fun_fun$ )(?v2 A$ )(?v3 A_a_tllist$ )(?v4 A$ )(?v5 A_a_tllist$ ))(! (= (tllist_all2$ ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$c ?v4 ?v5 ))(and (fun_app$j (fun_app$k ?v0 ?v2 )?v4 )(tllist_all2$ ?v0 ?v1 ?v3 ?v5 ))):pattern ((tllist_all2$ ?v0 ?v1 (tCons$c ?v2 ?v3 )(tCons$c ?v4 ?v5 ))))):named a61 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_b_fun$ )(?v2 A_a_tllist$ ))(= (ttl$ (tmap$a ?v0 ?v1 ?v2 ))(tmap$a ?v0 ?v1 (ttl$c ?v2 )))):named a62 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_a_fun$ )(?v2 A_b_tllist$ ))(= (ttl$c (tmap$b ?v0 ?v1 ?v2 ))(tmap$b ?v0 ?v1 (ttl$ ?v2 )))):named a63 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun$ )(?v2 A_a_tllist$ ))(= (ttl$c (tmap$c ?v0 ?v1 ?v2 ))(tmap$c ?v0 ?v1 (ttl$c ?v2 )))):named a64 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_tllist$ ))(= (ttl$ (tmap$ ?v0 ?v1 ?v2 ))(tmap$ ?v0 ?v1 (ttl$ ?v2 )))):named a65 ))
(check-sat )
;(get-unsat-core )
