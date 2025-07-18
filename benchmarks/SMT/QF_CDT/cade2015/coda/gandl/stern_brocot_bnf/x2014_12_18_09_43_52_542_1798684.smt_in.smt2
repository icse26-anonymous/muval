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
(declare-codatatypes ()((A_tree$ (node$ (root$ A$ )(left$ A_tree$ )(right$ A_tree$ )))(B_tree$ (node$a (root$a B$ )(left$a B_tree$ )(right$a B_tree$ )))))
(declare-fun f$ ()B_a_fun$ )
(declare-fun x$ ()B$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (B_a_fun$ B$ )A$ )
(declare-fun member$a (B$ B_set$ )Bool )
(declare-fun fun_app$a (A_a_fun$ A$ )A$ )
(declare-fun fun_app$b (A_b_fun$ A$ )B$ )
(declare-fun fun_app$c (B_b_fun$ B$ )B$ )
(declare-fun map_tree$ (B_a_fun$ B_tree$ )A_tree$ )
(declare-fun set_tree$ (A_tree$ )A_set$ )
(declare-fun map_tree$a (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun map_tree$b (A_b_fun$ A_tree$ )B_tree$ )
(declare-fun map_tree$c (B_b_fun$ B_tree$ )B_tree$ )
(declare-fun set_tree$a (B_tree$ )B_set$ )
(declare-fun tree_pure$ (B$ )B_tree$ )
(declare-fun tree_pure$a (A$ )A_tree$ )
(assert (! (not (= (map_tree$ f$ (tree_pure$ x$ ))(tree_pure$a (fun_app$ f$ x$ )))):named a0 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$a ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a1 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$b ?v0 ?v1 ))(fun_app$b ?v0 (root$ ?v1 )))):named a2 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$c ?v0 (root$a ?v1 )))):named a3 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$ ?v0 (root$a ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$a ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$b ?v0 ?v1 ))(fun_app$b ?v0 (root$ ?v1 )))):named a6 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$c ?v0 (root$a ?v1 )))):named a7 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$ ?v0 (root$a ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a10 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$a ?v1 )))):named a11 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$a ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$ ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$a ?v1 )))):named a15 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$a ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (right$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (right$ ?v1 )))):named a17 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (right$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (right$ ?v1 )))):named a18 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (right$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (right$a ?v1 )))):named a19 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (right$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (right$a ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (right$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (right$ ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (right$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (right$ ?v1 )))):named a22 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (right$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (right$a ?v1 )))):named a23 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (right$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (right$a ?v1 )))):named a24 ))
(assert (! (forall ((?v0 B$ ))(= (root$a (tree_pure$ ?v0 ))?v0 )):named a25 ))
(assert (! (forall ((?v0 A$ ))(= (root$ (tree_pure$a ?v0 ))?v0 )):named a26 ))
(assert (! (forall ((?v0 B$ ))(! (= (tree_pure$ ?v0 )(node$a ?v0 (tree_pure$ ?v0 )(tree_pure$ ?v0 ))):pattern ((tree_pure$ ?v0 )))):named a27 ))
(assert (! (forall ((?v0 A$ ))(! (= (tree_pure$a ?v0 )(node$ ?v0 (tree_pure$a ?v0 )(tree_pure$a ?v0 ))):pattern ((tree_pure$a ?v0 )))):named a28 ))
(assert (! (forall ((?v0 B$ ))(= (left$a (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a29 ))
(assert (! (forall ((?v0 A$ ))(= (left$ (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a30 ))
(assert (! (forall ((?v0 B$ ))(= (right$a (tree_pure$ ?v0 ))(tree_pure$ ?v0 ))):named a31 ))
(assert (! (forall ((?v0 A$ ))(= (right$ (tree_pure$a ?v0 ))(tree_pure$a ?v0 ))):named a32 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ )(?v2 A_b_fun$ )(?v3 A_b_fun$ ))(=> (and (forall ((?v4 A$ )(?v5 A$ ))(=> (and (member$ ?v4 (set_tree$ ?v0 ))(and (member$ ?v5 (set_tree$ ?v1 ))(= (fun_app$b ?v2 ?v4 )(fun_app$b ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (map_tree$b ?v2 ?v0 )(map_tree$b ?v3 ?v1 )))(= ?v0 ?v1 ))):named a33 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ )(?v2 A_a_fun$ )(?v3 A_a_fun$ ))(=> (and (forall ((?v4 A$ )(?v5 A$ ))(=> (and (member$ ?v4 (set_tree$ ?v0 ))(and (member$ ?v5 (set_tree$ ?v1 ))(= (fun_app$a ?v2 ?v4 )(fun_app$a ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (map_tree$a ?v2 ?v0 )(map_tree$a ?v3 ?v1 )))(= ?v0 ?v1 ))):named a34 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_tree$ )(?v2 B_b_fun$ )(?v3 B_b_fun$ ))(=> (and (forall ((?v4 B$ )(?v5 B$ ))(=> (and (member$a ?v4 (set_tree$a ?v0 ))(and (member$a ?v5 (set_tree$a ?v1 ))(= (fun_app$c ?v2 ?v4 )(fun_app$c ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (map_tree$c ?v2 ?v0 )(map_tree$c ?v3 ?v1 )))(= ?v0 ?v1 ))):named a35 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_tree$ )(?v2 B_a_fun$ )(?v3 B_a_fun$ ))(=> (and (forall ((?v4 B$ )(?v5 B$ ))(=> (and (member$a ?v4 (set_tree$a ?v0 ))(and (member$a ?v5 (set_tree$a ?v1 ))(= (fun_app$ ?v2 ?v4 )(fun_app$ ?v3 ?v5 ))))(= ?v4 ?v5 )))(= (map_tree$ ?v2 ?v0 )(map_tree$ ?v3 ?v1 )))(= ?v0 ?v1 ))):named a36 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_b_fun$ )(?v2 A_b_fun$ ))(=> (forall ((?v3 A$ ))(=> (member$ ?v3 (set_tree$ ?v0 ))(= (fun_app$b ?v1 ?v3 )(fun_app$b ?v2 ?v3 ))))(= (map_tree$b ?v1 ?v0 )(map_tree$b ?v2 ?v0 )))):named a37 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ ))(=> (forall ((?v3 A$ ))(=> (member$ ?v3 (set_tree$ ?v0 ))(= (fun_app$a ?v1 ?v3 )(fun_app$a ?v2 ?v3 ))))(= (map_tree$a ?v1 ?v0 )(map_tree$a ?v2 ?v0 )))):named a38 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ ))(=> (forall ((?v3 B$ ))(=> (member$a ?v3 (set_tree$a ?v0 ))(= (fun_app$c ?v1 ?v3 )(fun_app$c ?v2 ?v3 ))))(= (map_tree$c ?v1 ?v0 )(map_tree$c ?v2 ?v0 )))):named a39 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_a_fun$ )(?v2 B_a_fun$ ))(=> (forall ((?v3 B$ ))(=> (member$a ?v3 (set_tree$a ?v0 ))(= (fun_app$ ?v1 ?v3 )(fun_app$ ?v2 ?v3 ))))(= (map_tree$ ?v1 ?v0 )(map_tree$ ?v2 ?v0 )))):named a40 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a41 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(= (= (node$a ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a42 ))
(assert (! (forall ((?v0 A_tree$ ))(= (node$ (root$ ?v0 )(left$ ?v0 )(right$ ?v0 ))?v0 )):named a43 ))
(assert (! (forall ((?v0 B_tree$ ))(= (node$a (root$a ?v0 )(left$a ?v0 )(right$a ?v0 ))?v0 )):named a44 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (left$ (node$ ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a45 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (left$a (node$a ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a46 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (root$ (node$ ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (root$a (node$a ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a48 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (right$ (node$ ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a49 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (right$a (node$a ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a50 ))
(check-sat )
;(get-unsat-core )
