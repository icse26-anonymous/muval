;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_a_fun_a_fun$ 0 )
(declare-sort A_a_a_a_fun_fun_fun$ 0 )
(declare-sort A_a_a_fun_a_fun_fun$ 0 )
(declare-sort A_a_a_fun_fun_a_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort A_a_fun_a_fun_a_fun$ 0 )
(declare-sort A_a_a_fun_a_a_fun_fun_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_a_fun_fun$ 0 )
(declare-codatatypes ()((A_tree$ (node$ (root$ A$ )(left$ A_tree$ )(right$ A_tree$ )))(A_a_fun_a_a_fun_fun_tree$ (node$a (select$ A_a_fun_a_a_fun_fun$ )(selecta$ A_a_fun_a_a_fun_fun_tree$ )(selectb$ A_a_fun_a_a_fun_fun_tree$ )))(A_a_fun_a_fun_tree$ (node$b (selectc$ A_a_fun_a_fun$ )(selectd$ A_a_fun_a_fun_tree$ )(selecte$ A_a_fun_a_fun_tree$ )))(A_a_a_fun_fun_tree$ (node$c (selectf$ A_a_a_fun_fun$ )(selectg$ A_a_a_fun_fun_tree$ )(selecth$ A_a_a_fun_fun_tree$ )))(A_a_fun_tree$ (node$d (selecti$ A_a_fun$ )(selectj$ A_a_fun_tree$ )(selectk$ A_a_fun_tree$ )))))
(declare-sort Dir$ 0)
(declare-sort Dir_list$ 0)
(declare-fun l$ ()Dir$)
(declare-fun r$ ()Dir$)
(declare-fun nil$ ()Dir_list$)
(declare-fun hd$ (Dir_list$)Dir$)
(declare-fun tl$ (Dir_list$)Dir_list$)
(declare-fun cons$ (Dir$ Dir_list$ )Dir_list$)
(declare-codatatypes ()((A_a_a_fun_a_fun_fun_tree$ (node$e (selectl$ A_a_a_fun_a_fun_fun$ )(selectm$ A_a_a_fun_a_fun_fun_tree$ )(selectn$ A_a_a_fun_a_fun_fun_tree$ )))(A_a_a_a_fun_fun_fun_tree$ (node$f (selecto$ A_a_a_a_fun_fun_fun$ )(selectp$ A_a_a_a_fun_fun_fun_tree$ )(selectq$ A_a_a_a_fun_fun_fun_tree$ )))(A_a_fun_a_fun_a_fun_tree$ (node$g (selectr$ A_a_fun_a_fun_a_fun$ )(selects$ A_a_fun_a_fun_a_fun_tree$ )(selectt$ A_a_fun_a_fun_a_fun_tree$ )))(A_a_a_fun_fun_a_fun_tree$ (node$h (selectu$ A_a_a_fun_fun_a_fun$ )(selectv$ A_a_a_fun_fun_a_fun_tree$ )(selectw$ A_a_a_fun_fun_a_fun_tree$ )))(A_a_a_fun_a_a_fun_fun_fun_tree$ (node$i (selectx$ A_a_a_fun_a_a_fun_fun_fun$ )(selecty$ A_a_a_fun_a_a_fun_fun_fun_tree$ )(selectz$ A_a_a_fun_a_a_fun_fun_fun_tree$ )))(A_a_fun_a_a_fun_a_fun_fun_tree$ (node$j (selecua$ A_a_fun_a_a_fun_a_fun_fun$ )(selecub$ A_a_fun_a_a_fun_a_fun_fun_tree$ )(selecuc$ A_a_fun_a_a_fun_a_fun_fun_tree$ )))))
(declare-fun x$ ()A$ )
(declare-fun left$a (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun root$a (A_a_fun_tree$ )A_a_fun$ )
(declare-fun root$b (A_a_fun_a_a_fun_fun_tree$ )A_a_fun_a_a_fun_fun$ )
(declare-fun root$c (A_a_fun_a_fun_tree$ )A_a_fun_a_fun$ )
(declare-fun root$d (A_a_a_fun_fun_tree$ )A_a_a_fun_fun$ )
(declare-fun mirror$ (A_tree$ )A_tree$ )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun mirror$a (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun tree_ap$ (A_a_fun_tree$ A_tree$ )A_tree$ )
(declare-fun fun_app$a (A_a_a_fun_fun$ A$ )A_a_fun$ )
(declare-fun fun_app$b (A_a_fun_a_fun$ A_a_fun$ )A$ )
(declare-fun fun_app$c (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun fun_app$d (A_a_a_fun_a_fun_fun$ A$ )A_a_fun_a_fun$ )
(declare-fun fun_app$e (A_a_a_a_fun_fun_fun$ A$ )A_a_a_fun_fun$ )
(declare-fun fun_app$f (A_a_fun_a_fun_a_fun$ A_a_fun_a_fun$ )A$ )
(declare-fun fun_app$g (A_a_a_fun_fun_a_fun$ A_a_a_fun_fun$ )A$ )
(declare-fun fun_app$h (A_a_a_fun_a_a_fun_fun_fun$ A$ )A_a_fun_a_a_fun_fun$ )
(declare-fun fun_app$i (A_a_fun_a_a_fun_a_fun_fun$ A_a_fun$ )A_a_fun_a_fun$ )
(declare-fun map_tree$ (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun tree_ap$a (A_a_a_fun_fun_tree$ A_tree$ )A_a_fun_tree$ )
(declare-fun tree_ap$b (A_a_fun_a_fun_tree$ A_a_fun_tree$ )A_tree$ )
(declare-fun tree_ap$c (A_a_fun_a_a_fun_fun_tree$ A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun tree_ap$d (A_a_a_fun_a_fun_fun_tree$ A_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun tree_ap$e (A_a_a_a_fun_fun_fun_tree$ A_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun tree_ap$f (A_a_fun_a_fun_a_fun_tree$ A_a_fun_a_fun_tree$ )A_tree$ )
(declare-fun tree_ap$g (A_a_a_fun_fun_a_fun_tree$ A_a_a_fun_fun_tree$ )A_tree$ )
(declare-fun tree_ap$h (A_a_a_fun_a_a_fun_fun_fun_tree$ A_tree$ )A_a_fun_a_a_fun_fun_tree$ )
(declare-fun tree_ap$i (A_a_fun_a_a_fun_a_fun_fun_tree$ A_a_fun_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun map_tree$a (A_a_a_fun_fun$ A_tree$ )A_a_fun_tree$ )
(declare-fun map_tree$b (A_a_fun_a_fun$ A_a_fun_tree$ )A_tree$ )
(declare-fun map_tree$c (A_a_fun_a_a_fun_fun$ A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun map_tree$d (A_a_a_fun_a_fun_fun$ A_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun map_tree$e (A_a_a_a_fun_fun_fun$ A_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun map_tree$f (A_a_fun_a_fun_a_fun$ A_a_fun_a_fun_tree$ )A_tree$ )
(declare-fun map_tree$g (A_a_a_fun_fun_a_fun$ A_a_a_fun_fun_tree$ )A_tree$ )
(declare-fun map_tree$h (A_a_a_fun_a_a_fun_fun_fun$ A_tree$ )A_a_fun_a_a_fun_fun_tree$ )
(declare-fun map_tree$i (A_a_fun_a_a_fun_a_fun_fun$ A_a_fun_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun tree_chop$ (A_a_fun_a_a_fun_fun_tree$ )A_a_fun_a_a_fun_fun_tree$ )
(declare-fun tree_pure$ (A$ )A_tree$ )
(declare-fun tree_chop$a (A_a_fun_a_fun_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun tree_chop$b (A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun tree_chop$c (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun tree_chop$d (A_tree$ )A_tree$ )
(declare-fun tree_pure$a (A_a_fun_a_a_fun_fun$ )A_a_fun_a_a_fun_fun_tree$ )
(declare-fun tree_pure$b (A_a_fun_a_fun$ )A_a_fun_a_fun_tree$ )
(declare-fun tree_pure$c (A_a_a_fun_fun$ )A_a_a_fun_fun_tree$ )
(declare-fun tree_pure$d (A_a_fun$ )A_a_fun_tree$ )
(declare-fun tree_pure$e (A_a_a_fun_a_fun_fun$ )A_a_a_fun_a_fun_fun_tree$ )
(declare-fun tree_pure$f (A_a_a_a_fun_fun_fun$ )A_a_a_a_fun_fun_fun_tree$ )
(declare-fun tree_pure$g (A_a_fun_a_fun_a_fun$ )A_a_fun_a_fun_a_fun_tree$ )
(declare-fun tree_pure$h (A_a_a_fun_fun_a_fun$ )A_a_a_fun_fun_a_fun_tree$ )
(declare-fun tree_pure$i (A_a_a_fun_a_a_fun_fun_fun$ )A_a_a_fun_a_a_fun_fun_fun_tree$ )
(declare-fun tree_pure$j (A_a_fun_a_a_fun_a_fun_fun$ )A_a_fun_a_a_fun_a_fun_fun_tree$ )
(declare-fun traverse_tree$ (Dir_list$ A_a_fun_a_a_fun_fun_tree$ )A_a_fun_a_a_fun_fun_tree$ )
(declare-fun traverse_tree$a (Dir_list$ A_a_fun_a_fun_tree$ )A_a_fun_a_fun_tree$ )
(declare-fun traverse_tree$b (Dir_list$ A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun traverse_tree$c (Dir_list$ A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun traverse_tree$d (Dir_list$ A_tree$ )A_tree$ )
(assert (! (not (= (mirror$ (tree_pure$ x$ ))(tree_pure$ x$ ))):named a0 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun_a_a_fun_fun$ ))(= (= (tree_pure$a ?v0 )(tree_pure$a ?v1 ))(= ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun_a_fun$ ))(= (= (tree_pure$b ?v0 )(tree_pure$b ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_a_a_fun_fun$ ))(= (= (tree_pure$c ?v0 )(tree_pure$c ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun$ ))(= (= (tree_pure$d ?v0 )(tree_pure$d ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (= (tree_pure$ ?v0 )(tree_pure$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ ))(= (mirror$a (node$d ?v0 ?v1 ?v2 ))(node$d ?v0 (mirror$a ?v2 )(mirror$a ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(= (mirror$ (node$ ?v0 ?v1 ?v2 ))(node$ ?v0 (mirror$ ?v2 )(mirror$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_a_fun_tree$ ))(= (root$a (mirror$a ?v0 ))(root$a ?v0 ))):named a8 ))
(assert (! (forall ((?v0 A_tree$ ))(= (root$ (mirror$ ?v0 ))(root$ ?v0 ))):named a9 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 A_a_fun_a_a_fun_fun$ ))(= (traverse_tree$ ?v0 (tree_pure$a ?v1 ))(tree_pure$a ?v1 ))):named a10 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 A_a_fun_a_fun$ ))(= (traverse_tree$a ?v0 (tree_pure$b ?v1 ))(tree_pure$b ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 A_a_a_fun_fun$ ))(= (traverse_tree$b ?v0 (tree_pure$c ?v1 ))(tree_pure$c ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 A_a_fun$ ))(= (traverse_tree$c ?v0 (tree_pure$d ?v1 ))(tree_pure$d ?v1 ))):named a13 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 A$ ))(= (traverse_tree$d ?v0 (tree_pure$ ?v1 ))(tree_pure$ ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ ))(= (tree_chop$ (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a15 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ ))(= (tree_chop$a (tree_pure$b ?v0 ))(tree_pure$b ?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(= (tree_chop$b (tree_pure$c ?v0 ))(tree_pure$c ?v0 ))):named a17 ))
(assert (! (forall ((?v0 A_a_fun$ ))(= (tree_chop$c (tree_pure$d ?v0 ))(tree_pure$d ?v0 ))):named a18 ))
(assert (! (forall ((?v0 A$ ))(= (tree_chop$d (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a19 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (tree_ap$ (tree_pure$d ?v0 )(tree_pure$ ?v1 ))(tree_pure$ (fun_app$ ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A$ ))(= (tree_ap$a (tree_pure$c ?v0 )(tree_pure$ ?v1 ))(tree_pure$d (fun_app$a ?v0 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun$ ))(= (tree_ap$b (tree_pure$b ?v0 )(tree_pure$d ?v1 ))(tree_pure$ (fun_app$b ?v0 ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun$ ))(= (tree_ap$c (tree_pure$a ?v0 )(tree_pure$d ?v1 ))(tree_pure$d (fun_app$c ?v0 ?v1 )))):named a23 ))
(assert (! (forall ((?v0 A_a_a_fun_a_fun_fun$ )(?v1 A$ ))(= (tree_ap$d (tree_pure$e ?v0 )(tree_pure$ ?v1 ))(tree_pure$b (fun_app$d ?v0 ?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_a_a_a_fun_fun_fun$ )(?v1 A$ ))(= (tree_ap$e (tree_pure$f ?v0 )(tree_pure$ ?v1 ))(tree_pure$c (fun_app$e ?v0 ?v1 )))):named a25 ))
(assert (! (forall ((?v0 A_a_fun_a_fun_a_fun$ )(?v1 A_a_fun_a_fun$ ))(= (tree_ap$f (tree_pure$g ?v0 )(tree_pure$b ?v1 ))(tree_pure$ (fun_app$f ?v0 ?v1 )))):named a26 ))
(assert (! (forall ((?v0 A_a_a_fun_fun_a_fun$ )(?v1 A_a_a_fun_fun$ ))(= (tree_ap$g (tree_pure$h ?v0 )(tree_pure$c ?v1 ))(tree_pure$ (fun_app$g ?v0 ?v1 )))):named a27 ))
(assert (! (forall ((?v0 A_a_a_fun_a_a_fun_fun_fun$ )(?v1 A$ ))(= (tree_ap$h (tree_pure$i ?v0 )(tree_pure$ ?v1 ))(tree_pure$a (fun_app$h ?v0 ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_a_fun_fun$ )(?v1 A_a_fun$ ))(= (tree_ap$i (tree_pure$j ?v0 )(tree_pure$d ?v1 ))(tree_pure$b (fun_app$i ?v0 ?v1 )))):named a29 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (map_tree$ ?v0 (tree_pure$ ?v1 ))(tree_pure$ (fun_app$ ?v0 ?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A$ ))(= (map_tree$a ?v0 (tree_pure$ ?v1 ))(tree_pure$d (fun_app$a ?v0 ?v1 )))):named a31 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun$ ))(= (map_tree$b ?v0 (tree_pure$d ?v1 ))(tree_pure$ (fun_app$b ?v0 ?v1 )))):named a32 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun$ ))(= (map_tree$c ?v0 (tree_pure$d ?v1 ))(tree_pure$d (fun_app$c ?v0 ?v1 )))):named a33 ))
(assert (! (forall ((?v0 A_a_a_fun_a_fun_fun$ )(?v1 A$ ))(= (map_tree$d ?v0 (tree_pure$ ?v1 ))(tree_pure$b (fun_app$d ?v0 ?v1 )))):named a34 ))
(assert (! (forall ((?v0 A_a_a_a_fun_fun_fun$ )(?v1 A$ ))(= (map_tree$e ?v0 (tree_pure$ ?v1 ))(tree_pure$c (fun_app$e ?v0 ?v1 )))):named a35 ))
(assert (! (forall ((?v0 A_a_fun_a_fun_a_fun$ )(?v1 A_a_fun_a_fun$ ))(= (map_tree$f ?v0 (tree_pure$b ?v1 ))(tree_pure$ (fun_app$f ?v0 ?v1 )))):named a36 ))
(assert (! (forall ((?v0 A_a_a_fun_fun_a_fun$ )(?v1 A_a_a_fun_fun$ ))(= (map_tree$g ?v0 (tree_pure$c ?v1 ))(tree_pure$ (fun_app$g ?v0 ?v1 )))):named a37 ))
(assert (! (forall ((?v0 A_a_a_fun_a_a_fun_fun_fun$ )(?v1 A$ ))(= (map_tree$h ?v0 (tree_pure$ ?v1 ))(tree_pure$a (fun_app$h ?v0 ?v1 )))):named a38 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_a_fun_fun$ )(?v1 A_a_fun$ ))(= (map_tree$i ?v0 (tree_pure$d ?v1 ))(tree_pure$b (fun_app$i ?v0 ?v1 )))):named a39 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ ))(! (= (tree_pure$a ?v0 )(node$a ?v0 (tree_pure$a ?v0 )(tree_pure$a ?v0 ))):pattern ((tree_pure$a ?v0 )))):named a40 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ ))(! (= (tree_pure$b ?v0 )(node$b ?v0 (tree_pure$b ?v0 )(tree_pure$b ?v0 ))):pattern ((tree_pure$b ?v0 )))):named a41 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(! (= (tree_pure$c ?v0 )(node$c ?v0 (tree_pure$c ?v0 )(tree_pure$c ?v0 ))):pattern ((tree_pure$c ?v0 )))):named a42 ))
(assert (! (forall ((?v0 A_a_fun$ ))(! (= (tree_pure$d ?v0 )(node$d ?v0 (tree_pure$d ?v0 )(tree_pure$d ?v0 ))):pattern ((tree_pure$d ?v0 )))):named a43 ))
(assert (! (forall ((?v0 A$ ))(! (= (tree_pure$ ?v0 )(node$ ?v0 (tree_pure$ ?v0 )(tree_pure$ ?v0 ))):pattern ((tree_pure$ ?v0 )))):named a44 ))
(assert (! (forall ((?v0 A_tree$ ))(= (left$ (mirror$ ?v0 ))(mirror$ (right$ ?v0 )))):named a45 ))
(assert (! (forall ((?v0 A_tree$ ))(= (right$ (mirror$ ?v0 ))(mirror$ (left$ ?v0 )))):named a46 ))
(assert (! (forall ((?v0 A_a_a_fun_fun_tree$ )(?v1 A_a_a_fun_fun_tree$ ))(=> (forall ((?v2 A$ ))(= (tree_ap$a ?v0 (tree_pure$ ?v2 ))(tree_ap$a ?v1 (tree_pure$ ?v2 ))))(= ?v0 ?v1 ))):named a47 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun_tree$ )(?v1 A_a_fun_a_a_fun_fun_tree$ ))(=> (forall ((?v2 A_a_fun$ ))(= (tree_ap$c ?v0 (tree_pure$d ?v2 ))(tree_ap$c ?v1 (tree_pure$d ?v2 ))))(= ?v0 ?v1 ))):named a48 ))
(assert (! (forall ((?v0 A_a_fun_a_fun_tree$ )(?v1 A_a_fun_a_fun_tree$ ))(=> (forall ((?v2 A_a_fun$ ))(= (tree_ap$b ?v0 (tree_pure$d ?v2 ))(tree_ap$b ?v1 (tree_pure$d ?v2 ))))(= ?v0 ?v1 ))):named a49 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_a_fun_tree$ ))(=> (forall ((?v2 A$ ))(= (tree_ap$ ?v0 (tree_pure$ ?v2 ))(tree_ap$ ?v1 (tree_pure$ ?v2 ))))(= ?v0 ?v1 ))):named a50 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ ))(= (root$b (tree_pure$a ?v0 ))?v0 )):named a51 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ ))(= (root$c (tree_pure$b ?v0 ))?v0 )):named a52 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ ))(= (root$d (tree_pure$c ?v0 ))?v0 )):named a53 ))
(assert (! (forall ((?v0 A_a_fun$ ))(= (root$a (tree_pure$d ?v0 ))?v0 )):named a54 ))
(assert (! (forall ((?v0 A$ ))(= (root$ (tree_pure$ ?v0 ))?v0 )):named a55 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ )(?v3 A_a_fun$ )(?v4 A_a_fun_tree$ )(?v5 A_a_fun_tree$ ))(= (= (node$d ?v0 ?v1 ?v2 )(node$d ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a56 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a57 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$c ?v0 (root$a ?v1 )))):named a58 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun_tree$ ))(= (root$ (map_tree$b ?v0 ?v1 ))(fun_app$b ?v0 (root$a ?v1 )))):named a59 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$a ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a60 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$ ?v0 (root$ ?v1 )))):named a61 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$c ?v0 (root$a ?v1 )))):named a62 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun_tree$ ))(= (root$ (map_tree$b ?v0 ?v1 ))(fun_app$b ?v0 (root$a ?v1 )))):named a63 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$a ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a64 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$ ?v0 (root$ ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun_tree$ ))(= (left$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$a ?v1 )))):named a66 ))
(assert (! (forall ((?v0 A_a_fun_a_fun$ )(?v1 A_a_fun_tree$ ))(= (left$ (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$a ?v1 )))):named a67 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$ ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$ ?v1 )))):named a69 ))
(check-sat )
;(get-unsat-core )
