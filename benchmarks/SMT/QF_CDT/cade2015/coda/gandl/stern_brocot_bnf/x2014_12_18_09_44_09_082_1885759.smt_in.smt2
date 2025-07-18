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
(declare-sort A_a_fun_set$ 0 )
(declare-sort A_b_fun_set$ 0 )
(declare-sort B_a_fun_set$ 0 )
(declare-sort B_b_fun_set$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun$ 0 )
(declare-sort A_a_fun_a_fun$ 0 )
(declare-sort A_a_fun_b_fun$ 0 )
(declare-sort A_b_fun_a_fun$ 0 )
(declare-sort A_b_fun_b_fun$ 0 )
(declare-sort B_a_a_fun_fun$ 0 )
(declare-sort B_a_b_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun_set$ 0 )
(declare-sort A_b_fun_a_b_fun_fun$ 0 )
(declare-sort A_b_fun_a_b_fun_fun_set$ 0 )
(declare-sort A_a_b_fun_a_b_fun_fun_fun$ 0 )
(declare-sort B_a_b_fun_a_b_fun_fun_fun$ 0 )
(declare-sort A_a_b_fun_a_b_fun_fun_fun_set$ 0 )
(declare-codatatypes ()((B_tree$ (node$ (root$ B$ )(left$ B_tree$ )(right$ B_tree$ )))(A_b_fun_tree$ (node$a (select$ A_b_fun$ )(selecta$ A_b_fun_tree$ )(selectb$ A_b_fun_tree$ )))(A_tree$ (node$b (root$a A$ )(left$a A_tree$ )(right$a A_tree$ )))(A_b_fun_a_b_fun_fun_tree$ (node$c (selectc$ A_b_fun_a_b_fun_fun$ )(selectd$ A_b_fun_a_b_fun_fun_tree$ )(selecte$ A_b_fun_a_b_fun_fun_tree$ )))(B_b_fun_tree$ (node$d (selectf$ B_b_fun$ )(selectg$ B_b_fun_tree$ )(selecth$ B_b_fun_tree$ )))(B_a_fun_tree$ (node$e (selecti$ B_a_fun$ )(selectj$ B_a_fun_tree$ )(selectk$ B_a_fun_tree$ )))(A_a_fun_tree$ (node$f (selectl$ A_a_fun$ )(selectm$ A_a_fun_tree$ )(selectn$ A_a_fun_tree$ )))(B_a_b_fun_fun_tree$ (node$g (selecto$ B_a_b_fun_fun$ )(selectp$ B_a_b_fun_fun_tree$ )(selectq$ B_a_b_fun_fun_tree$ )))(A_a_b_fun_fun_tree$ (node$h (selectr$ A_a_b_fun_fun$ )(selects$ A_a_b_fun_fun_tree$ )(selectt$ A_a_b_fun_fun_tree$ )))(A_b_fun_b_fun_tree$ (node$i (selectu$ A_b_fun_b_fun$ )(selectv$ A_b_fun_b_fun_tree$ )(selectw$ A_b_fun_b_fun_tree$ )))(A_b_fun_a_fun_tree$ (node$j (selectx$ A_b_fun_a_fun$ )(selecty$ A_b_fun_a_fun_tree$ )(selectz$ A_b_fun_a_fun_tree$ )))(B_a_b_fun_a_b_fun_fun_fun_tree$ (node$k (selecua$ B_a_b_fun_a_b_fun_fun_fun$ )(selecub$ B_a_b_fun_a_b_fun_fun_fun_tree$ )(selecuc$ B_a_b_fun_a_b_fun_fun_fun_tree$ )))(A_a_a_fun_fun_tree$ (node$l (selecud$ A_a_a_fun_fun$ )(selecue$ A_a_a_fun_fun_tree$ )(selecuf$ A_a_a_fun_fun_tree$ )))(A_a_fun_a_fun_tree$ (node$m (selecug$ A_a_fun_a_fun$ )(selecuh$ A_a_fun_a_fun_tree$ )(selecui$ A_a_fun_a_fun_tree$ )))(A_a_fun_b_fun_tree$ (node$n (selecuj$ A_a_fun_b_fun$ )(selecuk$ A_a_fun_b_fun_tree$ )(selecul$ A_a_fun_b_fun_tree$ )))(B_a_a_fun_fun_tree$ (node$o (selecum$ B_a_a_fun_fun$ )(selecun$ B_a_a_fun_fun_tree$ )(selecuo$ B_a_a_fun_fun_tree$ )))(A_a_b_fun_a_b_fun_fun_fun_tree$ (node$p (selecup$ A_a_b_fun_a_b_fun_fun_fun$ )(selecuq$ A_a_b_fun_a_b_fun_fun_fun_tree$ )(selecur$ A_a_b_fun_a_b_fun_fun_fun_tree$ )))))
(declare-fun x$ ()A$ )
(declare-fun fa$ ()A_b_fun_tree$ )
(declare-fun ga$ ()A_b_fun_tree$ )
(declare-fun left$b (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun left$c (A_b_fun_a_b_fun_fun_tree$ )A_b_fun_a_b_fun_fun_tree$ )
(declare-fun left$d (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun left$e (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun left$f (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun left$g (B_a_b_fun_fun_tree$ )B_a_b_fun_fun_tree$ )
(declare-fun left$h (A_a_b_fun_fun_tree$ )A_a_b_fun_fun_tree$ )
(declare-fun left$i (A_b_fun_b_fun_tree$ )A_b_fun_b_fun_tree$ )
(declare-fun left$j (A_b_fun_a_fun_tree$ )A_b_fun_a_fun_tree$ )
(declare-fun left$k (B_a_b_fun_a_b_fun_fun_fun_tree$ )B_a_b_fun_a_b_fun_fun_fun_tree$ )
(declare-fun left$l (B_a_a_fun_fun_tree$ )B_a_a_fun_fun_tree$ )
(declare-fun left$m (A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun left$n (A_a_b_fun_a_b_fun_fun_fun_tree$ )A_a_b_fun_a_b_fun_fun_fun_tree$ )
(declare-fun root$b (A_b_fun_tree$ )A_b_fun$ )
(declare-fun root$c (B_a_a_fun_fun_tree$ )B_a_a_fun_fun$ )
(declare-fun root$d (B_b_fun_tree$ )B_b_fun$ )
(declare-fun root$e (B_a_fun_tree$ )B_a_fun$ )
(declare-fun root$f (A_a_b_fun_fun_tree$ )A_a_b_fun_fun$ )
(declare-fun root$g (A_a_a_fun_fun_tree$ )A_a_a_fun_fun$ )
(declare-fun root$h (A_a_fun_tree$ )A_a_fun$ )
(declare-fun member$ (B_b_fun$ B_b_fun_set$ )Bool )
(declare-fun right$b (B_a_a_fun_fun_tree$ )B_a_a_fun_fun_tree$ )
(declare-fun right$c (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun right$d (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun right$e (A_a_b_fun_fun_tree$ )A_a_b_fun_fun_tree$ )
(declare-fun right$f (A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun right$g (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun right$h (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun fun_app$ (A_b_fun$ A$ )B$ )
(declare-fun member$a (B_a_fun$ B_a_fun_set$ )Bool )
(declare-fun member$b (A_a_b_fun_a_b_fun_fun_fun$ A_a_b_fun_a_b_fun_fun_fun_set$ )Bool )
(declare-fun member$c (A_a_b_fun_fun$ A_a_b_fun_fun_set$ )Bool )
(declare-fun member$d (A_a_fun$ A_a_fun_set$ )Bool )
(declare-fun member$e (A_b_fun_a_b_fun_fun$ A_b_fun_a_b_fun_fun_set$ )Bool )
(declare-fun member$f (B$ B_set$ )Bool )
(declare-fun member$g (A$ A_set$ )Bool )
(declare-fun member$h (A_b_fun$ A_b_fun_set$ )Bool )
(declare-fun tree_ap$ (A_b_fun_tree$ A_tree$ )B_tree$ )
(declare-fun fun_app$a (A_a_fun$ A$ )A$ )
(declare-fun fun_app$b (B_a_fun$ B$ )A$ )
(declare-fun fun_app$c (B_b_fun$ B$ )B$ )
(declare-fun fun_app$d (A_a_a_fun_fun$ A$ )A_a_fun$ )
(declare-fun fun_app$e (A_a_b_fun_fun$ A$ )A_b_fun$ )
(declare-fun fun_app$f (A_a_fun_a_fun$ A_a_fun$ )A$ )
(declare-fun fun_app$g (A_a_fun_b_fun$ A_a_fun$ )B$ )
(declare-fun fun_app$h (A_b_fun_a_fun$ A_b_fun$ )A$ )
(declare-fun fun_app$i (A_b_fun_b_fun$ A_b_fun$ )B$ )
(declare-fun map_tree$ (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun set_tree$ (B_b_fun_tree$ )B_b_fun_set$ )
(declare-fun tree_ap$a (A_b_fun_a_b_fun_fun_tree$ A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun tree_ap$b (B_b_fun_tree$ B_tree$ )B_tree$ )
(declare-fun tree_ap$c (B_a_fun_tree$ B_tree$ )A_tree$ )
(declare-fun tree_ap$d (A_a_fun_tree$ A_tree$ )A_tree$ )
(declare-fun tree_ap$e (B_a_b_fun_fun_tree$ B_tree$ )A_b_fun_tree$ )
(declare-fun tree_ap$f (A_a_b_fun_fun_tree$ A_tree$ )A_b_fun_tree$ )
(declare-fun tree_ap$g (A_b_fun_b_fun_tree$ A_b_fun_tree$ )B_tree$ )
(declare-fun tree_ap$h (A_b_fun_a_fun_tree$ A_b_fun_tree$ )A_tree$ )
(declare-fun tree_ap$i (B_a_b_fun_a_b_fun_fun_fun_tree$ B_tree$ )A_b_fun_a_b_fun_fun_tree$ )
(declare-fun tree_ap$j (A_a_a_fun_fun_tree$ A_tree$ )A_a_fun_tree$ )
(declare-fun tree_ap$k (A_a_fun_a_fun_tree$ A_a_fun_tree$ )A_tree$ )
(declare-fun tree_ap$l (A_a_fun_b_fun_tree$ A_a_fun_tree$ )B_tree$ )
(declare-fun map_tree$a (A_b_fun$ A_tree$ )B_tree$ )
(declare-fun map_tree$b (B_a_fun$ B_tree$ )A_tree$ )
(declare-fun map_tree$c (B_b_fun$ B_tree$ )B_tree$ )
(declare-fun map_tree$d (A_a_a_fun_fun$ A_tree$ )A_a_fun_tree$ )
(declare-fun map_tree$e (A_a_b_fun_fun$ A_tree$ )A_b_fun_tree$ )
(declare-fun map_tree$f (A_a_fun_a_fun$ A_a_fun_tree$ )A_tree$ )
(declare-fun map_tree$g (A_a_fun_b_fun$ A_a_fun_tree$ )B_tree$ )
(declare-fun map_tree$h (A_b_fun_a_fun$ A_b_fun_tree$ )A_tree$ )
(declare-fun map_tree$i (A_b_fun_b_fun$ A_b_fun_tree$ )B_tree$ )
(declare-fun map_tree$j (A_b_fun_a_b_fun_fun$ A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun map_tree$k (B_a_b_fun_fun$ B_tree$ )A_b_fun_tree$ )
(declare-fun map_tree$l (B_a_b_fun_a_b_fun_fun_fun$ B_tree$ )A_b_fun_a_b_fun_fun_tree$ )
(declare-fun set_tree$a (B_a_fun_tree$ )B_a_fun_set$ )
(declare-fun set_tree$b (A_a_b_fun_a_b_fun_fun_fun_tree$ )A_a_b_fun_a_b_fun_fun_fun_set$ )
(declare-fun set_tree$c (A_a_b_fun_fun_tree$ )A_a_b_fun_fun_set$ )
(declare-fun set_tree$d (A_a_fun_tree$ )A_a_fun_set$ )
(declare-fun set_tree$e (A_b_fun_a_b_fun_fun_tree$ )A_b_fun_a_b_fun_fun_set$ )
(declare-fun set_tree$f (B_tree$ )B_set$ )
(declare-fun set_tree$g (A_tree$ )A_set$ )
(declare-fun set_tree$h (A_b_fun_tree$ )A_b_fun_set$ )
(declare-fun tree_pure$ (A$ )A_tree$ )
(declare-fun tree_pure$a (A_b_fun$ )A_b_fun_tree$ )
(declare-fun tree_pure$b (B$ )B_tree$ )
(declare-fun tree_pure$c (A_a_fun$ )A_a_fun_tree$ )
(declare-fun tree_pure$d (B_a_fun$ )B_a_fun_tree$ )
(declare-fun tree_pure$e (B_b_fun$ )B_b_fun_tree$ )
(declare-fun tree_pure$f (A_a_a_fun_fun$ )A_a_a_fun_fun_tree$ )
(declare-fun tree_pure$g (A_a_b_fun_fun$ )A_a_b_fun_fun_tree$ )
(declare-fun tree_pure$h (A_a_fun_a_fun$ )A_a_fun_a_fun_tree$ )
(declare-fun tree_pure$i (A_a_fun_b_fun$ )A_a_fun_b_fun_tree$ )
(declare-fun tree_pure$j (A_b_fun_a_fun$ )A_b_fun_a_fun_tree$ )
(declare-fun tree_pure$k (A_b_fun_b_fun$ )A_b_fun_b_fun_tree$ )
(declare-fun tree_pure$l (A_b_fun_a_b_fun_fun$ )A_b_fun_a_b_fun_fun_tree$ )
(declare-fun tree_pure$m (B_a_a_fun_fun$ )B_a_a_fun_fun_tree$ )
(assert (! (not (= (tree_ap$ (left$b fa$ )(tree_pure$ x$ ))(tree_ap$ (left$b ga$ )(tree_pure$ x$ )))):named a0 ))
(assert (! (forall ((?v0 A$ ))(= (tree_ap$ fa$ (tree_pure$ ?v0 ))(tree_ap$ ga$ (tree_pure$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_b_fun_tree$ )(?v1 A_tree$ ))(= (left$ (tree_ap$ ?v0 ?v1 ))(tree_ap$ (left$b ?v0 )(left$a ?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun_tree$ )(?v1 A_b_fun_tree$ ))(= (left$b (tree_ap$a ?v0 ?v1 ))(tree_ap$a (left$c ?v0 )(left$b ?v1 )))):named a3 ))
(assert (! (forall ((?v0 B_b_fun_tree$ )(?v1 B_tree$ ))(= (left$ (tree_ap$b ?v0 ?v1 ))(tree_ap$b (left$d ?v0 )(left$ ?v1 )))):named a4 ))
(assert (! (forall ((?v0 B_a_fun_tree$ )(?v1 B_tree$ ))(= (left$a (tree_ap$c ?v0 ?v1 ))(tree_ap$c (left$e ?v0 )(left$ ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_tree$ ))(= (left$a (tree_ap$d ?v0 ?v1 ))(tree_ap$d (left$f ?v0 )(left$a ?v1 )))):named a6 ))
(assert (! (forall ((?v0 B_a_b_fun_fun_tree$ )(?v1 B_tree$ ))(= (left$b (tree_ap$e ?v0 ?v1 ))(tree_ap$e (left$g ?v0 )(left$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_a_b_fun_fun_tree$ )(?v1 A_tree$ ))(= (left$b (tree_ap$f ?v0 ?v1 ))(tree_ap$f (left$h ?v0 )(left$a ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_b_fun_b_fun_tree$ )(?v1 A_b_fun_tree$ ))(= (left$ (tree_ap$g ?v0 ?v1 ))(tree_ap$g (left$i ?v0 )(left$b ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_b_fun_a_fun_tree$ )(?v1 A_b_fun_tree$ ))(= (left$a (tree_ap$h ?v0 ?v1 ))(tree_ap$h (left$j ?v0 )(left$b ?v1 )))):named a10 ))
(assert (! (forall ((?v0 B_a_b_fun_a_b_fun_fun_fun_tree$ )(?v1 B_tree$ ))(= (left$c (tree_ap$i ?v0 ?v1 ))(tree_ap$i (left$k ?v0 )(left$ ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ ))(= (tree_ap$ (tree_pure$a ?v0 )(tree_pure$ ?v1 ))(tree_pure$b (fun_app$ ?v0 ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (tree_ap$d (tree_pure$c ?v0 )(tree_pure$ ?v1 ))(tree_pure$ (fun_app$a ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ ))(= (tree_ap$c (tree_pure$d ?v0 )(tree_pure$b ?v1 ))(tree_pure$ (fun_app$b ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (tree_ap$b (tree_pure$e ?v0 )(tree_pure$b ?v1 ))(tree_pure$b (fun_app$c ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A$ ))(= (tree_ap$j (tree_pure$f ?v0 )(tree_pure$ ?v1 ))(tree_pure$c (fun_app$d ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A$ ))(= (tree_ap$f (tree_pure$g ?v0 )(tree_pure$ ?v1 ))(tree_pure$a (fun_app$e ?v0 ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun$ ))(= (tree_ap$k (tree_pure$h ?v0 )(tree_pure$c ?v1 ))(tree_pure$ (fun_app$f ?v0 ?v1 )))):named a18 ))
(assert (! (forall ((?v0 A_a_fun_b_fun$ )(?v1 A_a_fun$ ))(= (tree_ap$l (tree_pure$i ?v0 )(tree_pure$c ?v1 ))(tree_pure$b (fun_app$g ?v0 ?v1 )))):named a19 ))
(assert (! (forall ((?v0 A_b_fun_a_fun$ )(?v1 A_b_fun$ ))(= (tree_ap$h (tree_pure$j ?v0 )(tree_pure$a ?v1 ))(tree_pure$ (fun_app$h ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_b_fun_b_fun$ )(?v1 A_b_fun$ ))(= (tree_ap$g (tree_pure$k ?v0 )(tree_pure$a ?v1 ))(tree_pure$b (fun_app$i ?v0 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A$ ))(= (left$a (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a22 ))
(assert (! (forall ((?v0 A_b_fun$ ))(= (left$b (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a23 ))
(assert (! (forall ((?v0 B$ ))(= (left$ (tree_pure$b ?v0 ))(tree_pure$b ?v0 ))):named a24 ))
(assert (! (forall ((?v0 A_a_fun$ ))(= (left$f (tree_pure$c ?v0 ))(tree_pure$c ?v0 ))):named a25 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ ))(= (left$c (tree_pure$l ?v0 ))(tree_pure$l ?v0 ))):named a26 ))
(assert (! (forall ((?v0 B_b_fun$ ))(= (left$d (tree_pure$e ?v0 ))(tree_pure$e ?v0 ))):named a27 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (left$e (tree_pure$d ?v0 ))(tree_pure$d ?v0 ))):named a28 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ ))(= (left$l (tree_pure$m ?v0 ))(tree_pure$m ?v0 ))):named a29 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(= (left$h (tree_pure$g ?v0 ))(tree_pure$g ?v0 ))):named a30 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(= (left$m (tree_pure$f ?v0 ))(tree_pure$f ?v0 ))):named a31 ))
(assert (! (= (root$b fa$ )(root$b ga$ )):named a32 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (map_tree$ ?v0 (tree_pure$ ?v1 ))(tree_pure$ (fun_app$a ?v0 ?v1 )))):named a33 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ ))(= (map_tree$a ?v0 (tree_pure$ ?v1 ))(tree_pure$b (fun_app$ ?v0 ?v1 )))):named a34 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ ))(= (map_tree$b ?v0 (tree_pure$b ?v1 ))(tree_pure$ (fun_app$b ?v0 ?v1 )))):named a35 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (map_tree$c ?v0 (tree_pure$b ?v1 ))(tree_pure$b (fun_app$c ?v0 ?v1 )))):named a36 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A$ ))(= (map_tree$d ?v0 (tree_pure$ ?v1 ))(tree_pure$c (fun_app$d ?v0 ?v1 )))):named a37 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A$ ))(= (map_tree$e ?v0 (tree_pure$ ?v1 ))(tree_pure$a (fun_app$e ?v0 ?v1 )))):named a38 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun$ ))(= (map_tree$f ?v0 (tree_pure$c ?v1 ))(tree_pure$ (fun_app$f ?v0 ?v1 )))):named a39 ))
(assert (! (forall ((?v0 A_a_fun_b_fun$ )(?v1 A_a_fun$ ))(= (map_tree$g ?v0 (tree_pure$c ?v1 ))(tree_pure$b (fun_app$g ?v0 ?v1 )))):named a40 ))
(assert (! (forall ((?v0 A_b_fun_a_fun$ )(?v1 A_b_fun$ ))(= (map_tree$h ?v0 (tree_pure$a ?v1 ))(tree_pure$ (fun_app$h ?v0 ?v1 )))):named a41 ))
(assert (! (forall ((?v0 A_b_fun_b_fun$ )(?v1 A_b_fun$ ))(= (map_tree$i ?v0 (tree_pure$a ?v1 ))(tree_pure$b (fun_app$i ?v0 ?v1 )))):named a42 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ )(?v1 A_b_fun_tree$ ))(= (left$b (map_tree$j ?v0 ?v1 ))(map_tree$j ?v0 (left$b ?v1 )))):named a43 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$ ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a45 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a46 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$a ?v1 )))):named a47 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B_tree$ ))(= (left$b (map_tree$k ?v0 ?v1 ))(map_tree$k ?v0 (left$ ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_tree$ ))(= (left$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (left$a ?v1 )))):named a49 ))
(assert (! (forall ((?v0 A_b_fun_b_fun$ )(?v1 A_b_fun_tree$ ))(= (left$ (map_tree$i ?v0 ?v1 ))(map_tree$i ?v0 (left$b ?v1 )))):named a50 ))
(assert (! (forall ((?v0 A_b_fun_a_fun$ )(?v1 A_b_fun_tree$ ))(= (left$a (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (left$b ?v1 )))):named a51 ))
(assert (! (forall ((?v0 B_a_b_fun_a_b_fun_fun_fun$ )(?v1 B_tree$ ))(= (left$c (map_tree$l ?v0 ?v1 ))(map_tree$l ?v0 (left$ ?v1 )))):named a52 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ )(?v1 A_b_fun_tree$ ))(= (left$b (map_tree$j ?v0 ?v1 ))(map_tree$j ?v0 (left$b ?v1 )))):named a53 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$ ?v1 )))):named a54 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a55 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a56 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$a ?v1 )))):named a57 ))
(assert (! (forall ((?v0 B_a_b_fun_fun$ )(?v1 B_tree$ ))(= (left$b (map_tree$k ?v0 ?v1 ))(map_tree$k ?v0 (left$ ?v1 )))):named a58 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_tree$ ))(= (left$b (map_tree$e ?v0 ?v1 ))(map_tree$e ?v0 (left$a ?v1 )))):named a59 ))
(assert (! (forall ((?v0 A_b_fun_b_fun$ )(?v1 A_b_fun_tree$ ))(= (left$ (map_tree$i ?v0 ?v1 ))(map_tree$i ?v0 (left$b ?v1 )))):named a60 ))
(assert (! (forall ((?v0 A_b_fun_a_fun$ )(?v1 A_b_fun_tree$ ))(= (left$a (map_tree$h ?v0 ?v1 ))(map_tree$h ?v0 (left$b ?v1 )))):named a61 ))
(assert (! (forall ((?v0 B_a_b_fun_a_b_fun_fun_fun$ )(?v1 B_tree$ ))(= (left$c (map_tree$l ?v0 ?v1 ))(map_tree$l ?v0 (left$ ?v1 )))):named a62 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ ))(= (root$c (tree_pure$m ?v0 ))?v0 )):named a63 ))
(assert (! (forall ((?v0 B_b_fun$ ))(= (root$d (tree_pure$e ?v0 ))?v0 )):named a64 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (root$e (tree_pure$d ?v0 ))?v0 )):named a65 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(= (root$f (tree_pure$g ?v0 ))?v0 )):named a66 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(= (root$g (tree_pure$f ?v0 ))?v0 )):named a67 ))
(assert (! (forall ((?v0 A_a_fun$ ))(= (root$h (tree_pure$c ?v0 ))?v0 )):named a68 ))
(assert (! (forall ((?v0 B$ ))(= (root$ (tree_pure$b ?v0 ))?v0 )):named a69 ))
(assert (! (forall ((?v0 A_b_fun$ ))(= (root$b (tree_pure$a ?v0 ))?v0 )):named a70 ))
(assert (! (forall ((?v0 A$ ))(= (root$a (tree_pure$ ?v0 ))?v0 )):named a71 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ ))(= (right$b (tree_pure$m ?v0 ))(tree_pure$m ?v0 ))):named a72 ))
(assert (! (forall ((?v0 B_b_fun$ ))(= (right$c (tree_pure$e ?v0 ))(tree_pure$e ?v0 ))):named a73 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (right$d (tree_pure$d ?v0 ))(tree_pure$d ?v0 ))):named a74 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(= (right$e (tree_pure$g ?v0 ))(tree_pure$g ?v0 ))):named a75 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(= (right$f (tree_pure$f ?v0 ))(tree_pure$f ?v0 ))):named a76 ))
(assert (! (forall ((?v0 A_a_fun$ ))(= (right$g (tree_pure$c ?v0 ))(tree_pure$c ?v0 ))):named a77 ))
(assert (! (forall ((?v0 A_b_fun$ ))(= (right$h (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a78 ))
(assert (! (forall ((?v0 B$ ))(= (right$ (tree_pure$b ?v0 ))(tree_pure$b ?v0 ))):named a79 ))
(assert (! (forall ((?v0 A$ ))(= (right$a (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a80 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ ))(! (= (tree_pure$l ?v0 )(node$c ?v0 (tree_pure$l ?v0 )(tree_pure$l ?v0 ))):pattern ((tree_pure$l ?v0 )))):named a81 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ ))(! (= (tree_pure$m ?v0 )(node$o ?v0 (tree_pure$m ?v0 )(tree_pure$m ?v0 ))):pattern ((tree_pure$m ?v0 )))):named a82 ))
(assert (! (forall ((?v0 B_b_fun$ ))(! (= (tree_pure$e ?v0 )(node$d ?v0 (tree_pure$e ?v0 )(tree_pure$e ?v0 ))):pattern ((tree_pure$e ?v0 )))):named a83 ))
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (tree_pure$d ?v0 )(node$e ?v0 (tree_pure$d ?v0 )(tree_pure$d ?v0 ))):pattern ((tree_pure$d ?v0 )))):named a84 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(! (= (tree_pure$g ?v0 )(node$h ?v0 (tree_pure$g ?v0 )(tree_pure$g ?v0 ))):pattern ((tree_pure$g ?v0 )))):named a85 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(! (= (tree_pure$f ?v0 )(node$l ?v0 (tree_pure$f ?v0 )(tree_pure$f ?v0 ))):pattern ((tree_pure$f ?v0 )))):named a86 ))
(assert (! (forall ((?v0 A_a_fun$ ))(! (= (tree_pure$c ?v0 )(node$f ?v0 (tree_pure$c ?v0 )(tree_pure$c ?v0 ))):pattern ((tree_pure$c ?v0 )))):named a87 ))
(assert (! (forall ((?v0 A_b_fun$ ))(! (= (tree_pure$a ?v0 )(node$a ?v0 (tree_pure$a ?v0 )(tree_pure$a ?v0 ))):pattern ((tree_pure$a ?v0 )))):named a88 ))
(assert (! (forall ((?v0 B$ ))(! (= (tree_pure$b ?v0 )(node$ ?v0 (tree_pure$b ?v0 )(tree_pure$b ?v0 ))):pattern ((tree_pure$b ?v0 )))):named a89 ))
(assert (! (forall ((?v0 A$ ))(! (= (tree_pure$ ?v0 )(node$b ?v0 (tree_pure$ ?v0 )(tree_pure$ ?v0 ))):pattern ((tree_pure$ ?v0 )))):named a90 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ ))(=> (member$ ?v0 (set_tree$ (left$d ?v1 )))(member$ ?v0 (set_tree$ ?v1 )))):named a91 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ ))(=> (member$a ?v0 (set_tree$a (left$e ?v1 )))(member$a ?v0 (set_tree$a ?v1 )))):named a92 ))
(assert (! (forall ((?v0 A_a_b_fun_a_b_fun_fun_fun$ )(?v1 A_a_b_fun_a_b_fun_fun_fun_tree$ ))(=> (member$b ?v0 (set_tree$b (left$n ?v1 )))(member$b ?v0 (set_tree$b ?v1 )))):named a93 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_a_b_fun_fun_tree$ ))(=> (member$c ?v0 (set_tree$c (left$h ?v1 )))(member$c ?v0 (set_tree$c ?v1 )))):named a94 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ ))(=> (member$d ?v0 (set_tree$d (left$f ?v1 )))(member$d ?v0 (set_tree$d ?v1 )))):named a95 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ )(?v1 A_b_fun_a_b_fun_fun_tree$ ))(=> (member$e ?v0 (set_tree$e (left$c ?v1 )))(member$e ?v0 (set_tree$e ?v1 )))):named a96 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ ))(=> (member$f ?v0 (set_tree$f (left$ ?v1 )))(member$f ?v0 (set_tree$f ?v1 )))):named a97 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (member$g ?v0 (set_tree$g (left$a ?v1 )))(member$g ?v0 (set_tree$g ?v1 )))):named a98 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ ))(=> (member$h ?v0 (set_tree$h (left$b ?v1 )))(member$h ?v0 (set_tree$h ?v1 )))):named a99 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ ))(=> (member$ ?v0 (set_tree$ (left$d ?v1 )))(member$ ?v0 (set_tree$ ?v1 )))):named a100 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ ))(=> (member$a ?v0 (set_tree$a (left$e ?v1 )))(member$a ?v0 (set_tree$a ?v1 )))):named a101 ))
(assert (! (forall ((?v0 A_a_b_fun_a_b_fun_fun_fun$ )(?v1 A_a_b_fun_a_b_fun_fun_fun_tree$ ))(=> (member$b ?v0 (set_tree$b (left$n ?v1 )))(member$b ?v0 (set_tree$b ?v1 )))):named a102 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_a_b_fun_fun_tree$ ))(=> (member$c ?v0 (set_tree$c (left$h ?v1 )))(member$c ?v0 (set_tree$c ?v1 )))):named a103 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ ))(=> (member$d ?v0 (set_tree$d (left$f ?v1 )))(member$d ?v0 (set_tree$d ?v1 )))):named a104 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ )(?v1 A_b_fun_a_b_fun_fun_tree$ ))(=> (member$e ?v0 (set_tree$e (left$c ?v1 )))(member$e ?v0 (set_tree$e ?v1 )))):named a105 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ ))(=> (member$f ?v0 (set_tree$f (left$ ?v1 )))(member$f ?v0 (set_tree$f ?v1 )))):named a106 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (member$g ?v0 (set_tree$g (left$a ?v1 )))(member$g ?v0 (set_tree$g ?v1 )))):named a107 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ ))(=> (member$h ?v0 (set_tree$h (left$b ?v1 )))(member$h ?v0 (set_tree$h ?v1 )))):named a108 ))
(assert (! (forall ((?v0 A_a_b_fun_a_b_fun_fun_fun$ )(?v1 A_a_b_fun_a_b_fun_fun_fun_tree$ )(?v2 A_a_b_fun_a_b_fun_fun_fun_tree$ ))(! (= (left$n (node$p ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$p ?v0 ?v1 ?v2 )))):named a109 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_a_b_fun_fun_tree$ )(?v2 A_a_b_fun_fun_tree$ ))(! (= (left$h (node$h ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$h ?v0 ?v1 ?v2 )))):named a110 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ ))(! (= (left$f (node$f ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$f ?v0 ?v1 ?v2 )))):named a111 ))
(assert (! (forall ((?v0 A_b_fun_a_b_fun_fun$ )(?v1 A_b_fun_a_b_fun_fun_tree$ )(?v2 A_b_fun_a_b_fun_fun_tree$ ))(! (= (left$c (node$c ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$c ?v0 ?v1 ?v2 )))):named a112 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (left$ (node$ ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a113 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (left$a (node$b ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$b ?v0 ?v1 ?v2 )))):named a114 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ ))(! (= (left$b (node$a ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a115 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$b ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a116 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ )(?v3 A_b_fun$ )(?v4 A_b_fun_tree$ )(?v5 A_b_fun_tree$ ))(= (= (node$a ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a117 ))
(check-sat )
;(get-unsat-core )
