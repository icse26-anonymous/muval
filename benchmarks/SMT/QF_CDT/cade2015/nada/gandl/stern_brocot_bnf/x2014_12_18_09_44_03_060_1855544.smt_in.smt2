;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_b_a_fun_fun$ 0 )
(declare-sort B_a_fun_a_fun$ 0 )
(declare-sort B_a_fun_b_fun$ 0 )
(declare-sort B_b_a_fun_fun$ 0 )
(declare-sort B_b_b_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-sort B_a_fun_tree$ 0)
(declare-sort B_tree$ 0)
(declare-sort B_b_fun_tree$ 0)
(declare-sort A_b_fun_tree$ 0)
(declare-sort A_a_fun_tree$ 0)
(declare-sort B_b_a_fun_fun_tree$ 0)
(declare-sort A_b_a_fun_fun_tree$ 0)
(declare-sort B_a_fun_b_fun_tree$ 0)
(declare-sort B_a_fun_a_fun_tree$ 0)
(declare-sort B_a_fun_b_a_fun_fun_tree$ 0)
(declare-sort B_b_b_fun_fun_tree$ 0)
(declare-fun root$ (A_tree$)A$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A$ A_tree$ A_tree$ )A_tree$)
(declare-fun select$ (B_a_fun_tree$)B_a_fun$)
(declare-fun selecta$ (B_a_fun_tree$)B_a_fun_tree$)
(declare-fun selectb$ (B_a_fun_tree$)B_a_fun_tree$)
(declare-fun node$a (B_a_fun$ B_a_fun_tree$ B_a_fun_tree$ )B_a_fun_tree$)
(declare-fun root$a (B_tree$)B$)
(declare-fun left$a (B_tree$)B_tree$)
(declare-fun right$a (B_tree$)B_tree$)
(declare-fun node$b (B$ B_tree$ B_tree$ )B_tree$)
(declare-fun selectc$ (B_b_fun_tree$)B_b_fun$)
(declare-fun selectd$ (B_b_fun_tree$)B_b_fun_tree$)
(declare-fun selecte$ (B_b_fun_tree$)B_b_fun_tree$)
(declare-fun node$c (B_b_fun$ B_b_fun_tree$ B_b_fun_tree$ )B_b_fun_tree$)
(declare-fun selectf$ (A_b_fun_tree$)A_b_fun$)
(declare-fun selectg$ (A_b_fun_tree$)A_b_fun_tree$)
(declare-fun selecth$ (A_b_fun_tree$)A_b_fun_tree$)
(declare-fun node$d (A_b_fun$ A_b_fun_tree$ A_b_fun_tree$ )A_b_fun_tree$)
(declare-fun selecti$ (A_a_fun_tree$)A_a_fun$)
(declare-fun selectj$ (A_a_fun_tree$)A_a_fun_tree$)
(declare-fun selectk$ (A_a_fun_tree$)A_a_fun_tree$)
(declare-fun node$e (A_a_fun$ A_a_fun_tree$ A_a_fun_tree$ )A_a_fun_tree$)
(declare-fun selectl$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun$)
(declare-fun selectm$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun_tree$)
(declare-fun selectn$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun_tree$)
(declare-fun node$f (B_b_a_fun_fun$ B_b_a_fun_fun_tree$ B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$)
(declare-fun selecto$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun$)
(declare-fun selectp$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun_tree$)
(declare-fun selectq$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun_tree$)
(declare-fun node$g (A_b_a_fun_fun$ A_b_a_fun_fun_tree$ A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$)
(declare-fun selectr$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun$)
(declare-fun selects$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun_tree$)
(declare-fun selectt$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun_tree$)
(declare-fun node$h (B_a_fun_b_fun$ B_a_fun_b_fun_tree$ B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$)
(declare-fun selectu$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun$)
(declare-fun selectv$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun_tree$)
(declare-fun selectw$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun_tree$)
(declare-fun node$i (B_a_fun_a_fun$ B_a_fun_a_fun_tree$ B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$)
(declare-fun selectx$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun$)
(declare-fun selecty$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun_tree$)
(declare-fun selectz$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun_tree$)
(declare-fun node$j (B_a_fun_b_a_fun_fun$ B_a_fun_b_a_fun_fun_tree$ B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$)
(declare-fun selecua$ (B_b_b_fun_fun_tree$)B_b_b_fun_fun$)
(declare-fun selecub$ (B_b_b_fun_fun_tree$)B_b_b_fun_fun_tree$)
(declare-fun selecuc$ (B_b_b_fun_fun_tree$)B_b_b_fun_fun_tree$)
(declare-fun node$k (B_b_b_fun_fun$ B_b_b_fun_fun_tree$ B_b_b_fun_fun_tree$ )B_b_b_fun_fun_tree$)
(declare-fun f$ ()B_a_fun$ )
(declare-fun x$ ()B$ )
(declare-fun id$ ()B_b_fun$ )
(declare-fun id$a ()A_a_fun$ )
(declare-fun left$b (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun left$c (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun left$d (B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$ )
(declare-fun left$e (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun left$f (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun left$g (B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$ )
(declare-fun left$h (A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$ )
(declare-fun left$i (B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$ )
(declare-fun left$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun root$b (B_a_fun_tree$ )B_a_fun$ )
(declare-fun root$c (A_a_fun_tree$ )A_a_fun$ )
(declare-fun root$d (B_a_fun_a_fun_tree$ )B_a_fun_a_fun$ )
(declare-fun root$e (A_b_fun_tree$ )A_b_fun$ )
(declare-fun root$f (B_b_fun_tree$ )B_b_fun$ )
(declare-fun root$g (B_a_fun_b_fun_tree$ )B_a_fun_b_fun$ )
(declare-fun root$h (A_b_a_fun_fun_tree$ )A_b_a_fun_fun$ )
(declare-fun root$i (B_b_a_fun_fun_tree$ )B_b_a_fun_fun$ )
(declare-fun root$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun$ )
(declare-fun right$b (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun right$c (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun right$d (B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$ )
(declare-fun right$e (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun right$f (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun right$g (B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$ )
(declare-fun right$h (A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$ )
(declare-fun right$i (B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$ )
(declare-fun right$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun fun_app$ (B_a_fun$ B$ )A$ )
(declare-fun tree_ap$ (B_a_fun_tree$ B_tree$ )A_tree$ )
(declare-fun fun_app$a (B_b_fun$ B$ )B$ )
(declare-fun fun_app$b (A_b_fun$ A$ )B$ )
(declare-fun fun_app$c (A_a_fun$ A$ )A$ )
(declare-fun fun_app$d (B_b_a_fun_fun$ B$ )B_a_fun$ )
(declare-fun fun_app$e (A_b_a_fun_fun$ A$ )B_a_fun$ )
(declare-fun fun_app$f (B_a_fun_b_fun$ B_a_fun$ )B$ )
(declare-fun fun_app$g (B_a_fun_a_fun$ B_a_fun$ )A$ )
(declare-fun fun_app$h (B_a_fun_b_a_fun_fun$ B_a_fun$ )B_a_fun$ )
(declare-fun fun_app$i (B_b_b_fun_fun$ B$ )B_b_fun$ )
(declare-fun map_tree$ (B_a_fun_b_a_fun_fun$ B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$a (B_b_fun_tree$ B_tree$ )B_tree$ )
(declare-fun tree_ap$b (A_b_fun_tree$ A_tree$ )B_tree$ )
(declare-fun tree_ap$c (A_a_fun_tree$ A_tree$ )A_tree$ )
(declare-fun tree_ap$d (B_b_a_fun_fun_tree$ B_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$e (A_b_a_fun_fun_tree$ A_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$f (B_a_fun_b_fun_tree$ B_a_fun_tree$ )B_tree$ )
(declare-fun tree_ap$g (B_a_fun_a_fun_tree$ B_a_fun_tree$ )A_tree$ )
(declare-fun tree_ap$h (B_a_fun_b_a_fun_fun_tree$ B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$i (B_b_b_fun_fun_tree$ B_tree$ )B_b_fun_tree$ )
(declare-fun map_tree$a (B_b_a_fun_fun$ B_tree$ )B_a_fun_tree$ )
(declare-fun map_tree$b (B_a_fun_b_fun$ B_a_fun_tree$ )B_tree$ )
(declare-fun map_tree$c (B_a_fun_a_fun$ B_a_fun_tree$ )A_tree$ )
(declare-fun map_tree$d (B_b_fun$ B_tree$ )B_tree$ )
(declare-fun map_tree$e (A_b_a_fun_fun$ A_tree$ )B_a_fun_tree$ )
(declare-fun map_tree$f (A_b_fun$ A_tree$ )B_tree$ )
(declare-fun map_tree$g (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun map_tree$h (B_a_fun$ B_tree$ )A_tree$ )
(declare-fun tree_pure$ (B_a_fun$ )B_a_fun_tree$ )
(declare-fun tree_pure$a (B$ )B_tree$ )
(declare-fun tree_pure$b (A$ )A_tree$ )
(declare-fun tree_pure$c (B_b_fun$ )B_b_fun_tree$ )
(declare-fun tree_pure$d (A_b_fun$ )A_b_fun_tree$ )
(declare-fun tree_pure$e (A_a_fun$ )A_a_fun_tree$ )
(declare-fun tree_pure$f (B_b_a_fun_fun$ )B_b_a_fun_fun_tree$ )
(declare-fun tree_pure$g (A_b_a_fun_fun$ )A_b_a_fun_fun_tree$ )
(declare-fun tree_pure$h (B_a_fun_b_fun$ )B_a_fun_b_fun_tree$ )
(declare-fun tree_pure$i (B_a_fun_a_fun$ )B_a_fun_a_fun_tree$ )
(declare-fun tree_pure$j (B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun tree_pure$k (B_b_b_fun_fun$ )B_b_b_fun_fun_tree$ )
(assert (! (not (= (tree_ap$ (tree_pure$ f$ )(tree_pure$a x$ ))(tree_pure$b (fun_app$ f$ x$ )))):named a0 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$ (tree_pure$ ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$ (fun_app$ ?v0 ?v1 )(tree_ap$ (tree_pure$ ?v0 )?v2 )(tree_ap$ (tree_pure$ ?v0 )?v3 )))):named a1 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$a (tree_pure$c ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$b (fun_app$a ?v0 ?v1 )(tree_ap$a (tree_pure$c ?v0 )?v2 )(tree_ap$a (tree_pure$c ?v0 )?v3 )))):named a2 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$b (tree_pure$d ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$b (fun_app$b ?v0 ?v1 )(tree_ap$b (tree_pure$d ?v0 )?v2 )(tree_ap$b (tree_pure$d ?v0 )?v3 )))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$c (tree_pure$e ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$ (fun_app$c ?v0 ?v1 )(tree_ap$c (tree_pure$e ?v0 )?v2 )(tree_ap$c (tree_pure$e ?v0 )?v3 )))):named a4 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$d (tree_pure$f ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$a (fun_app$d ?v0 ?v1 )(tree_ap$d (tree_pure$f ?v0 )?v2 )(tree_ap$d (tree_pure$f ?v0 )?v3 )))):named a5 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$e (tree_pure$g ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$a (fun_app$e ?v0 ?v1 )(tree_ap$e (tree_pure$g ?v0 )?v2 )(tree_ap$e (tree_pure$g ?v0 )?v3 )))):named a6 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$f (tree_pure$h ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$b (fun_app$f ?v0 ?v1 )(tree_ap$f (tree_pure$h ?v0 )?v2 )(tree_ap$f (tree_pure$h ?v0 )?v3 )))):named a7 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$g (tree_pure$i ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$ (fun_app$g ?v0 ?v1 )(tree_ap$g (tree_pure$i ?v0 )?v2 )(tree_ap$g (tree_pure$i ?v0 )?v3 )))):named a8 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$h (tree_pure$j ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$a (fun_app$h ?v0 ?v1 )(tree_ap$h (tree_pure$j ?v0 )?v2 )(tree_ap$h (tree_pure$j ?v0 )?v3 )))):named a9 ))
(assert (! (forall ((?v0 B_b_b_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$i (tree_pure$k ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$c (fun_app$i ?v0 ?v1 )(tree_ap$i (tree_pure$k ?v0 )?v2 )(tree_ap$i (tree_pure$k ?v0 )?v3 )))):named a10 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$h (tree_pure$j ?v0 )?v1 )(map_tree$ ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_tree$ ))(= (tree_ap$d (tree_pure$f ?v0 )?v1 )(map_tree$a ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$f (tree_pure$h ?v0 )?v1 )(map_tree$b ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$g (tree_pure$i ?v0 )?v1 )(map_tree$c ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (tree_ap$a (tree_pure$c ?v0 )?v1 )(map_tree$d ?v0 ?v1 ))):named a15 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_tree$ ))(= (tree_ap$e (tree_pure$g ?v0 )?v1 )(map_tree$e ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (tree_ap$b (tree_pure$d ?v0 )?v1 )(map_tree$f ?v0 ?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (tree_ap$c (tree_pure$e ?v0 )?v1 )(map_tree$g ?v0 ?v1 ))):named a18 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (tree_ap$ (tree_pure$ ?v0 )?v1 )(map_tree$h ?v0 ?v1 ))):named a19 ))
(assert (! (forall ((?v0 B_tree$ ))(= (tree_ap$a (tree_pure$c id$ )?v0 )?v0 )):named a20 ))
(assert (! (forall ((?v0 A_tree$ ))(= (tree_ap$c (tree_pure$e id$a )?v0 )?v0 )):named a21 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun$ ))(= (map_tree$ ?v0 (tree_pure$ ?v1 ))(tree_pure$ (fun_app$h ?v0 ?v1 )))):named a22 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun$ ))(= (map_tree$b ?v0 (tree_pure$ ?v1 ))(tree_pure$a (fun_app$f ?v0 ?v1 )))):named a23 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun$ ))(= (map_tree$c ?v0 (tree_pure$ ?v1 ))(tree_pure$b (fun_app$g ?v0 ?v1 )))):named a24 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B$ ))(= (map_tree$a ?v0 (tree_pure$a ?v1 ))(tree_pure$ (fun_app$d ?v0 ?v1 )))):named a25 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (map_tree$d ?v0 (tree_pure$a ?v1 ))(tree_pure$a (fun_app$a ?v0 ?v1 )))):named a26 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ ))(= (map_tree$h ?v0 (tree_pure$a ?v1 ))(tree_pure$b (fun_app$ ?v0 ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A$ ))(= (map_tree$e ?v0 (tree_pure$b ?v1 ))(tree_pure$ (fun_app$e ?v0 ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ ))(= (map_tree$f ?v0 (tree_pure$b ?v1 ))(tree_pure$a (fun_app$b ?v0 ?v1 )))):named a29 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (map_tree$g ?v0 (tree_pure$b ?v1 ))(tree_pure$b (fun_app$c ?v0 ?v1 )))):named a30 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (root$b (tree_pure$ ?v0 ))?v0 )):named a31 ))
(assert (! (forall ((?v0 B$ ))(= (root$a (tree_pure$a ?v0 ))?v0 )):named a32 ))
(assert (! (forall ((?v0 A$ ))(= (root$ (tree_pure$b ?v0 ))?v0 )):named a33 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (left$b (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a34 ))
(assert (! (forall ((?v0 B$ ))(= (left$a (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a35 ))
(assert (! (forall ((?v0 A$ ))(= (left$ (tree_pure$b ?v0 ))(tree_pure$b ?v0 ))):named a36 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (right$b (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a37 ))
(assert (! (forall ((?v0 B$ ))(= (right$a (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a38 ))
(assert (! (forall ((?v0 A$ ))(= (right$ (tree_pure$b ?v0 ))(tree_pure$b ?v0 ))):named a39 ))
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (tree_pure$ ?v0 )(node$a ?v0 (tree_pure$ ?v0 )(tree_pure$ ?v0 ))):pattern ((tree_pure$ ?v0 )))):named a40 ))
(assert (! (forall ((?v0 B$ ))(! (= (tree_pure$a ?v0 )(node$b ?v0 (tree_pure$a ?v0 )(tree_pure$a ?v0 ))):pattern ((tree_pure$a ?v0 )))):named a41 ))
(assert (! (forall ((?v0 A$ ))(! (= (tree_pure$b ?v0 )(node$ ?v0 (tree_pure$b ?v0 )(tree_pure$b ?v0 ))):pattern ((tree_pure$b ?v0 )))):named a42 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ )(?v2 B_b_fun_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(! (= (tree_ap$a (node$c ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(node$b (fun_app$a ?v0 ?v3 )(tree_ap$a ?v1 ?v4 )(tree_ap$a ?v2 ?v5 ))):pattern ((tree_ap$a (node$c ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))))):named a43 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_tree$ )(?v2 B_b_a_fun_fun_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(! (= (tree_ap$d (node$f ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(node$a (fun_app$d ?v0 ?v3 )(tree_ap$d ?v1 ?v4 )(tree_ap$d ?v2 ?v5 ))):pattern ((tree_ap$d (node$f ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))))):named a44 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(! (= (tree_ap$b (node$d ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(node$b (fun_app$b ?v0 ?v3 )(tree_ap$b ?v1 ?v4 )(tree_ap$b ?v2 ?v5 ))):pattern ((tree_ap$b (node$d ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))))):named a45 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(! (= (tree_ap$c (node$e ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(node$ (fun_app$c ?v0 ?v3 )(tree_ap$c ?v1 ?v4 )(tree_ap$c ?v2 ?v5 ))):pattern ((tree_ap$c (node$e ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))))):named a46 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(! (= (tree_ap$e (node$g ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(node$a (fun_app$e ?v0 ?v3 )(tree_ap$e ?v1 ?v4 )(tree_ap$e ?v2 ?v5 ))):pattern ((tree_ap$e (node$g ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))))):named a47 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_b_fun_tree$ )(?v2 B_a_fun_b_fun_tree$ )(?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(! (= (tree_ap$f (node$h ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(node$b (fun_app$f ?v0 ?v3 )(tree_ap$f ?v1 ?v4 )(tree_ap$f ?v2 ?v5 ))):pattern ((tree_ap$f (node$h ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))))):named a48 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_a_fun_tree$ )(?v2 B_a_fun_a_fun_tree$ )(?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(! (= (tree_ap$g (node$i ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(node$ (fun_app$g ?v0 ?v3 )(tree_ap$g ?v1 ?v4 )(tree_ap$g ?v2 ?v5 ))):pattern ((tree_ap$g (node$i ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))))):named a49 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_b_a_fun_fun_tree$ )(?v2 B_a_fun_b_a_fun_fun_tree$ )(?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(! (= (tree_ap$h (node$j ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(node$a (fun_app$h ?v0 ?v3 )(tree_ap$h ?v1 ?v4 )(tree_ap$h ?v2 ?v5 ))):pattern ((tree_ap$h (node$j ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))))):named a50 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(! (= (tree_ap$ (node$a ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(node$ (fun_app$ ?v0 ?v3 )(tree_ap$ ?v1 ?v4 )(tree_ap$ ?v2 ?v5 ))):pattern ((tree_ap$ (node$a ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))))):named a51 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_tree$ ))(= (root$ (tree_ap$c ?v0 ?v1 ))(fun_app$c (root$c ?v0 )(root$ ?v1 )))):named a52 ))
(assert (! (forall ((?v0 B_a_fun_a_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (root$ (tree_ap$g ?v0 ?v1 ))(fun_app$g (root$d ?v0 )(root$b ?v1 )))):named a53 ))
(assert (! (forall ((?v0 A_b_fun_tree$ )(?v1 A_tree$ ))(= (root$a (tree_ap$b ?v0 ?v1 ))(fun_app$b (root$e ?v0 )(root$ ?v1 )))):named a54 ))
(assert (! (forall ((?v0 B_b_fun_tree$ )(?v1 B_tree$ ))(= (root$a (tree_ap$a ?v0 ?v1 ))(fun_app$a (root$f ?v0 )(root$a ?v1 )))):named a55 ))
(assert (! (forall ((?v0 B_a_fun_b_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (root$a (tree_ap$f ?v0 ?v1 ))(fun_app$f (root$g ?v0 )(root$b ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ )(?v1 A_tree$ ))(= (root$b (tree_ap$e ?v0 ?v1 ))(fun_app$e (root$h ?v0 )(root$ ?v1 )))):named a57 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ )(?v1 B_tree$ ))(= (root$b (tree_ap$d ?v0 ?v1 ))(fun_app$d (root$i ?v0 )(root$a ?v1 )))):named a58 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (root$b (tree_ap$h ?v0 ?v1 ))(fun_app$h (root$j ?v0 )(root$b ?v1 )))):named a59 ))
(assert (! (forall ((?v0 B_a_fun_tree$ )(?v1 B_tree$ ))(= (root$ (tree_ap$ ?v0 ?v1 ))(fun_app$ (root$b ?v0 )(root$a ?v1 )))):named a60 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_tree$ ))(= (left$ (tree_ap$c ?v0 ?v1 ))(tree_ap$c (left$c ?v0 )(left$ ?v1 )))):named a61 ))
(assert (! (forall ((?v0 B_a_fun_a_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (left$ (tree_ap$g ?v0 ?v1 ))(tree_ap$g (left$d ?v0 )(left$b ?v1 )))):named a62 ))
(assert (! (forall ((?v0 A_b_fun_tree$ )(?v1 A_tree$ ))(= (left$a (tree_ap$b ?v0 ?v1 ))(tree_ap$b (left$e ?v0 )(left$ ?v1 )))):named a63 ))
(assert (! (forall ((?v0 B_b_fun_tree$ )(?v1 B_tree$ ))(= (left$a (tree_ap$a ?v0 ?v1 ))(tree_ap$a (left$f ?v0 )(left$a ?v1 )))):named a64 ))
(assert (! (forall ((?v0 B_a_fun_b_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (left$a (tree_ap$f ?v0 ?v1 ))(tree_ap$f (left$g ?v0 )(left$b ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ )(?v1 A_tree$ ))(= (left$b (tree_ap$e ?v0 ?v1 ))(tree_ap$e (left$h ?v0 )(left$ ?v1 )))):named a66 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ )(?v1 B_tree$ ))(= (left$b (tree_ap$d ?v0 ?v1 ))(tree_ap$d (left$i ?v0 )(left$a ?v1 )))):named a67 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (left$b (tree_ap$h ?v0 ?v1 ))(tree_ap$h (left$j ?v0 )(left$b ?v1 )))):named a68 ))
(assert (! (forall ((?v0 B_a_fun_tree$ )(?v1 B_tree$ ))(= (left$ (tree_ap$ ?v0 ?v1 ))(tree_ap$ (left$b ?v0 )(left$a ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_tree$ ))(= (right$ (tree_ap$c ?v0 ?v1 ))(tree_ap$c (right$c ?v0 )(right$ ?v1 )))):named a70 ))
(assert (! (forall ((?v0 B_a_fun_a_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (right$ (tree_ap$g ?v0 ?v1 ))(tree_ap$g (right$d ?v0 )(right$b ?v1 )))):named a71 ))
(assert (! (forall ((?v0 A_b_fun_tree$ )(?v1 A_tree$ ))(= (right$a (tree_ap$b ?v0 ?v1 ))(tree_ap$b (right$e ?v0 )(right$ ?v1 )))):named a72 ))
(assert (! (forall ((?v0 B_b_fun_tree$ )(?v1 B_tree$ ))(= (right$a (tree_ap$a ?v0 ?v1 ))(tree_ap$a (right$f ?v0 )(right$a ?v1 )))):named a73 ))
(assert (! (forall ((?v0 B_a_fun_b_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (right$a (tree_ap$f ?v0 ?v1 ))(tree_ap$f (right$g ?v0 )(right$b ?v1 )))):named a74 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ )(?v1 A_tree$ ))(= (right$b (tree_ap$e ?v0 ?v1 ))(tree_ap$e (right$h ?v0 )(right$ ?v1 )))):named a75 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ )(?v1 B_tree$ ))(= (right$b (tree_ap$d ?v0 ?v1 ))(tree_ap$d (right$i ?v0 )(right$a ?v1 )))):named a76 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (right$b (tree_ap$h ?v0 ?v1 ))(tree_ap$h (right$j ?v0 )(right$b ?v1 )))):named a77 ))
(assert (! (forall ((?v0 B_a_fun_tree$ )(?v1 B_tree$ ))(= (right$ (tree_ap$ ?v0 ?v1 ))(tree_ap$ (right$b ?v0 )(right$a ?v1 )))):named a78 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(= (= (node$b ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a79 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a80 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(= (= (node$a ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a81 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_tree$ ))(= (left$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$b ?v1 )))):named a82 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$b ?v1 )))):named a83 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_tree$ ))(= (left$b (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a84 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_tree$ ))(= (left$b (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$b ?v1 )))):named a85 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$d ?v0 ?v1 ))(map_tree$d ?v0 (left$a ?v1 )))):named a86 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (left$a ?v1 )))):named a87 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_tree$ ))(= (left$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (left$ ?v1 )))):named a88 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$f ?v0 ?v1 ))(map_tree$f ?v0 (left$ ?v1 )))):named a89 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$g ?v0 ?v1 ))(map_tree$g ?v0 (left$ ?v1 )))):named a90 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_tree$ ))(= (left$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$b ?v1 )))):named a91 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$b ?v1 )))):named a92 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_tree$ ))(= (left$b (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a93 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_tree$ ))(= (left$b (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$b ?v1 )))):named a94 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$d ?v0 ?v1 ))(map_tree$d ?v0 (left$a ?v1 )))):named a95 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (left$a ?v1 )))):named a96 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_tree$ ))(= (left$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (left$ ?v1 )))):named a97 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$f ?v0 ?v1 ))(map_tree$f ?v0 (left$ ?v1 )))):named a98 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$g ?v0 ?v1 ))(map_tree$g ?v0 (left$ ?v1 )))):named a99 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_tree$ ))(= (right$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (right$b ?v1 )))):named a100 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_tree$ ))(= (right$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (right$b ?v1 )))):named a101 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_tree$ ))(= (right$b (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (right$a ?v1 )))):named a102 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_tree$ ))(= (right$b (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (right$b ?v1 )))):named a103 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (right$a (map_tree$d ?v0 ?v1 ))(map_tree$d ?v0 (right$a ?v1 )))):named a104 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (right$ (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (right$a ?v1 )))):named a105 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_tree$ ))(= (right$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (right$ ?v1 )))):named a106 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (right$a (map_tree$f ?v0 ?v1 ))(map_tree$f ?v0 (right$ ?v1 )))):named a107 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (right$ (map_tree$g ?v0 ?v1 ))(map_tree$g ?v0 (right$ ?v1 )))):named a108 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun_tree$ ))(= (right$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (right$b ?v1 )))):named a109 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun_tree$ ))(= (right$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (right$b ?v1 )))):named a110 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_tree$ ))(= (right$b (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (right$a ?v1 )))):named a111 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun_tree$ ))(= (right$b (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (right$b ?v1 )))):named a112 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (right$a (map_tree$d ?v0 ?v1 ))(map_tree$d ?v0 (right$a ?v1 )))):named a113 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (right$ (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (right$a ?v1 )))):named a114 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_tree$ ))(= (right$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (right$ ?v1 )))):named a115 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (right$a (map_tree$f ?v0 ?v1 ))(map_tree$f ?v0 (right$ ?v1 )))):named a116 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (right$ (map_tree$g ?v0 ?v1 ))(map_tree$g ?v0 (right$ ?v1 )))):named a117 ))
(check-sat )
;(get-unsat-core )
