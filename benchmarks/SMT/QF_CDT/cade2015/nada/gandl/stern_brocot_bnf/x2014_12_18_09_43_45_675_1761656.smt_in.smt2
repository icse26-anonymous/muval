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
(declare-sort A_tree_a_fun$ 0 )
(declare-sort B_tree_b_fun$ 0 )
(declare-sort A_tree_bool_fun$ 0 )
(declare-sort B_tree_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort B_a_bool_fun_fun$ 0 )
(declare-sort B_b_bool_fun_fun$ 0 )
(declare-sort A_tree_a_tree_bool_fun_fun$ 0 )
(declare-sort A_tree_b_tree_bool_fun_fun$ 0 )
(declare-sort B_tree_a_tree_bool_fun_fun$ 0 )
(declare-sort B_tree_b_tree_bool_fun_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-sort B_tree$ 0)
(declare-fun root$ (A_tree$)A$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A$ A_tree$ A_tree$ )A_tree$)
(declare-fun root$a (B_tree$)B$)
(declare-fun left$a (B_tree$)B_tree$)
(declare-fun right$a (B_tree$)B_tree$)
(declare-fun node$a (B$ B_tree$ B_tree$ )B_tree$)
(declare-fun a$ ()A_b_bool_fun_fun$ )
(declare-fun x$ ()A_tree$ )
(declare-fun y$ ()B_tree$ )
(declare-fun uu$ ()B_b_bool_fun_fun$ )
(declare-fun uua$ ()B_tree_b_tree_bool_fun_fun$ )
(declare-fun uub$ ()A_a_bool_fun_fun$ )
(declare-fun uuc$ ()A_tree_a_tree_bool_fun_fun$ )
(declare-fun uud$ ()A_tree_a_fun$ )
(declare-fun uue$ ()B_tree_b_fun$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (B_tree_b_fun$ B_tree$ )B$ )
(declare-fun member$a (B$ B_set$ )Bool )
(declare-fun rel_fun$ (A_tree_a_tree_bool_fun_fun$ A_a_bool_fun_fun$ A_tree_a_fun$ A_tree_a_fun$ )Bool )
(declare-fun fun_app$a (A_tree_a_fun$ A_tree$ )A$ )
(declare-fun fun_app$b (B_tree_bool_fun$ B_tree$ )Bool )
(declare-fun fun_app$c (B_tree_b_tree_bool_fun_fun$ B_tree$ )B_tree_bool_fun$ )
(declare-fun fun_app$d (A_tree_bool_fun$ A_tree$ )Bool )
(declare-fun fun_app$e (A_tree_a_tree_bool_fun_fun$ A_tree$ )A_tree_bool_fun$ )
(declare-fun fun_app$f (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$g (B_b_bool_fun_fun$ B$ )B_bool_fun$ )
(declare-fun fun_app$h (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$i (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$j (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$k (A_tree_b_tree_bool_fun_fun$ A_tree$ )B_tree_bool_fun$ )
(declare-fun fun_app$l (A_a_fun$ A$ )A$ )
(declare-fun fun_app$m (B_a_fun$ B$ )A$ )
(declare-fun fun_app$n (A_b_fun$ A$ )B$ )
(declare-fun fun_app$o (B_b_fun$ B$ )B$ )
(declare-fun fun_app$p (B_tree_a_tree_bool_fun_fun$ B_tree$ )A_tree_bool_fun$ )
(declare-fun fun_app$q (B_a_bool_fun_fun$ B$ )A_bool_fun$ )
(declare-fun map_tree$ (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun rel_fun$a (B_tree_a_tree_bool_fun_fun$ B_a_bool_fun_fun$ B_tree_b_fun$ A_tree_a_fun$ )Bool )
(declare-fun rel_fun$b (B_tree_b_tree_bool_fun_fun$ B_b_bool_fun_fun$ B_tree_b_fun$ B_tree_b_fun$ )Bool )
(declare-fun rel_fun$c (A_tree_b_tree_bool_fun_fun$ A_b_bool_fun_fun$ A_tree_a_fun$ B_tree_b_fun$ )Bool )
(declare-fun rel_tree$ (A_b_bool_fun_fun$ )A_tree_b_tree_bool_fun_fun$ )
(declare-fun set_tree$ (A_tree$ )A_set$ )
(declare-fun map_tree$a (B_a_fun$ B_tree$ )A_tree$ )
(declare-fun map_tree$b (A_b_fun$ A_tree$ )B_tree$ )
(declare-fun map_tree$c (B_b_fun$ B_tree$ )B_tree$ )
(declare-fun rel_tree$a (B_b_bool_fun_fun$ )B_tree_b_tree_bool_fun_fun$ )
(declare-fun rel_tree$b (A_a_bool_fun_fun$ )A_tree_a_tree_bool_fun_fun$ )
(declare-fun rel_tree$c (B_a_bool_fun_fun$ )B_tree_a_tree_bool_fun_fun$ )
(declare-fun set_tree$a (B_tree$ )B_set$ )
(assert (! (forall ((?v0 B_tree$ ))(! (= (fun_app$ uue$ ?v0 )(root$a ?v0 )):pattern ((fun_app$ uue$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_tree$ ))(! (= (fun_app$a uud$ ?v0 )(root$ ?v0 )):pattern ((fun_app$a uud$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_tree$ ))(! (= (fun_app$b (fun_app$c uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uua$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ ))(! (= (fun_app$d (fun_app$e uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uuc$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 B$ )(?v1 B$ ))(! (= (fun_app$f (fun_app$g uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (fun_app$g uu$ ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$h (fun_app$i uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$h (fun_app$i uub$ ?v0 )?v1 )))):named a5 ))
(assert (! (not (fun_app$f (fun_app$j a$ (root$ x$ ))(root$a y$ ))):named a6 ))
(assert (! (fun_app$b (fun_app$k (rel_tree$ a$ )x$ )y$ ):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$l ?v0 (root$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (root$ (map_tree$a ?v0 ?v1 ))(fun_app$m ?v0 (root$a ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$b ?v0 ?v1 ))(fun_app$n ?v0 (root$ ?v1 )))):named a10 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$o ?v0 (root$a ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$l ?v0 (root$ ?v1 )))):named a12 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (root$ (map_tree$a ?v0 ?v1 ))(fun_app$m ?v0 (root$a ?v1 )))):named a13 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (root$a (map_tree$b ?v0 ?v1 ))(fun_app$n ?v0 (root$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (root$a (map_tree$c ?v0 ?v1 ))(fun_app$o ?v0 (root$a ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_tree$ ))(member$ (root$ ?v0 )(set_tree$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 B_tree$ ))(member$a (root$a ?v0 )(set_tree$a ?v0 ))):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (root$ (node$ ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a18 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (root$a (node$a ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a19 ))
(assert (! (= (rel_tree$a uu$ )uua$ ):named a20 ))
(assert (! (= (rel_tree$b uub$ )uuc$ ):named a21 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ ))(rel_fun$ (rel_tree$b ?v0 )?v0 uud$ uud$ )):named a22 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ ))(rel_fun$a (rel_tree$c ?v0 )?v0 uue$ uud$ )):named a23 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ ))(rel_fun$b (rel_tree$a ?v0 )?v0 uue$ uue$ )):named a24 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ ))(rel_fun$c (rel_tree$ ?v0 )?v0 uud$ uue$ )):named a25 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ ))(=> (and (= (root$ ?v0 )(root$ ?v1 ))(and (= (left$ ?v0 )(left$ ?v1 ))(= (right$ ?v0 )(right$ ?v1 ))))(= ?v0 ?v1 ))):named a26 ))
(assert (! (forall ((?v0 B_tree$ )(?v1 B_tree$ ))(=> (and (= (root$a ?v0 )(root$a ?v1 ))(and (= (left$a ?v0 )(left$a ?v1 ))(= (right$a ?v0 )(right$a ?v1 ))))(= ?v0 ?v1 ))):named a27 ))
(assert (! (forall ((?v0 A_tree_a_tree_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(=> (and (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 A_tree$ )(?v4 A_tree$ ))(=> (fun_app$d (fun_app$e ?v0 ?v3 )?v4 )(and (= (root$ ?v3 )(root$ ?v4 ))(and (or (fun_app$d (fun_app$e ?v0 (left$ ?v3 ))(left$ ?v4 ))(= (left$ ?v3 )(left$ ?v4 )))(or (fun_app$d (fun_app$e ?v0 (right$ ?v3 ))(right$ ?v4 ))(= (right$ ?v3 )(right$ ?v4 ))))))))(= ?v1 ?v2 ))):named a28 ))
(assert (! (forall ((?v0 B_tree_b_tree_bool_fun_fun$ )(?v1 B_tree$ )(?v2 B_tree$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 B_tree$ )(?v4 B_tree$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (root$a ?v3 )(root$a ?v4 ))(and (or (fun_app$b (fun_app$c ?v0 (left$a ?v3 ))(left$a ?v4 ))(= (left$a ?v3 )(left$a ?v4 )))(or (fun_app$b (fun_app$c ?v0 (right$a ?v3 ))(right$a ?v4 ))(= (right$a ?v3 )(right$a ?v4 ))))))))(= ?v1 ?v2 ))):named a29 ))
(assert (! (forall ((?v0 A_tree_a_tree_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(=> (and (fun_app$d (fun_app$e ?v0 ?v1 )?v2 )(forall ((?v3 A_tree$ )(?v4 A_tree$ ))(=> (fun_app$d (fun_app$e ?v0 ?v3 )?v4 )(and (= (root$ ?v3 )(root$ ?v4 ))(and (fun_app$d (fun_app$e ?v0 (left$ ?v3 ))(left$ ?v4 ))(fun_app$d (fun_app$e ?v0 (right$ ?v3 ))(right$ ?v4 )))))))(= ?v1 ?v2 ))):named a30 ))
(assert (! (forall ((?v0 B_tree_b_tree_bool_fun_fun$ )(?v1 B_tree$ )(?v2 B_tree$ ))(=> (and (fun_app$b (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 B_tree$ )(?v4 B_tree$ ))(=> (fun_app$b (fun_app$c ?v0 ?v3 )?v4 )(and (= (root$a ?v3 )(root$a ?v4 ))(and (fun_app$b (fun_app$c ?v0 (left$a ?v3 ))(left$a ?v4 ))(fun_app$b (fun_app$c ?v0 (right$a ?v3 ))(right$a ?v4 )))))))(= ?v1 ?v2 ))):named a31 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(= (fun_app$d (fun_app$e (rel_tree$b ?v0 )?v1 )?v2 )(and (fun_app$h (fun_app$i ?v0 (root$ ?v1 ))(root$ ?v2 ))(and (fun_app$d (fun_app$e (rel_tree$b ?v0 )(left$ ?v1 ))(left$ ?v2 ))(fun_app$d (fun_app$e (rel_tree$b ?v0 )(right$ ?v1 ))(right$ ?v2 )))))):named a32 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B_tree$ )(?v2 A_tree$ ))(= (fun_app$d (fun_app$p (rel_tree$c ?v0 )?v1 )?v2 )(and (fun_app$h (fun_app$q ?v0 (root$a ?v1 ))(root$ ?v2 ))(and (fun_app$d (fun_app$p (rel_tree$c ?v0 )(left$a ?v1 ))(left$ ?v2 ))(fun_app$d (fun_app$p (rel_tree$c ?v0 )(right$a ?v1 ))(right$ ?v2 )))))):named a33 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B_tree$ )(?v2 B_tree$ ))(= (fun_app$b (fun_app$c (rel_tree$a ?v0 )?v1 )?v2 )(and (fun_app$f (fun_app$g ?v0 (root$a ?v1 ))(root$a ?v2 ))(and (fun_app$b (fun_app$c (rel_tree$a ?v0 )(left$a ?v1 ))(left$a ?v2 ))(fun_app$b (fun_app$c (rel_tree$a ?v0 )(right$a ?v1 ))(right$a ?v2 )))))):named a34 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A_tree$ )(?v2 B_tree$ ))(= (fun_app$b (fun_app$k (rel_tree$ ?v0 )?v1 )?v2 )(and (fun_app$f (fun_app$j ?v0 (root$ ?v1 ))(root$a ?v2 ))(and (fun_app$b (fun_app$k (rel_tree$ ?v0 )(left$ ?v1 ))(left$a ?v2 ))(fun_app$b (fun_app$k (rel_tree$ ?v0 )(right$ ?v1 ))(right$a ?v2 )))))):named a35 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(= (= (node$a ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a36 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a37 ))
(assert (! (forall ((?v0 B_b_bool_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ )(?v4 B$ )(?v5 B_tree$ )(?v6 B_tree$ ))(! (= (fun_app$b (fun_app$c (rel_tree$a ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$a ?v4 ?v5 ?v6 ))(and (fun_app$f (fun_app$g ?v0 ?v1 )?v4 )(and (fun_app$b (fun_app$c (rel_tree$a ?v0 )?v2 )?v5 )(fun_app$b (fun_app$c (rel_tree$a ?v0 )?v3 )?v6 )))):pattern ((fun_app$b (fun_app$c (rel_tree$a ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$a ?v4 ?v5 ?v6 ))))):named a38 ))
(assert (! (forall ((?v0 B_a_bool_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ )(?v4 A$ )(?v5 A_tree$ )(?v6 A_tree$ ))(! (= (fun_app$d (fun_app$p (rel_tree$c ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$ ?v4 ?v5 ?v6 ))(and (fun_app$h (fun_app$q ?v0 ?v1 )?v4 )(and (fun_app$d (fun_app$p (rel_tree$c ?v0 )?v2 )?v5 )(fun_app$d (fun_app$p (rel_tree$c ?v0 )?v3 )?v6 )))):pattern ((fun_app$d (fun_app$p (rel_tree$c ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$ ?v4 ?v5 ?v6 ))))):named a39 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ )(?v4 A$ )(?v5 A_tree$ )(?v6 A_tree$ ))(! (= (fun_app$d (fun_app$e (rel_tree$b ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$ ?v4 ?v5 ?v6 ))(and (fun_app$h (fun_app$i ?v0 ?v1 )?v4 )(and (fun_app$d (fun_app$e (rel_tree$b ?v0 )?v2 )?v5 )(fun_app$d (fun_app$e (rel_tree$b ?v0 )?v3 )?v6 )))):pattern ((fun_app$d (fun_app$e (rel_tree$b ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$ ?v4 ?v5 ?v6 ))))):named a40 ))
(assert (! (forall ((?v0 A_b_bool_fun_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ )(?v4 B$ )(?v5 B_tree$ )(?v6 B_tree$ ))(! (= (fun_app$b (fun_app$k (rel_tree$ ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$a ?v4 ?v5 ?v6 ))(and (fun_app$f (fun_app$j ?v0 ?v1 )?v4 )(and (fun_app$b (fun_app$k (rel_tree$ ?v0 )?v2 )?v5 )(fun_app$b (fun_app$k (rel_tree$ ?v0 )?v3 )?v6 )))):pattern ((fun_app$b (fun_app$k (rel_tree$ ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$a ?v4 ?v5 ?v6 ))))):named a41 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$a ?v1 )))):named a42 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a43 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$ ?v1 )))):named a45 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_tree$ ))(= (left$a (map_tree$c ?v0 ?v1 ))(map_tree$c ?v0 (left$a ?v1 )))):named a46 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_tree$ ))(= (left$a (map_tree$b ?v0 ?v1 ))(map_tree$b ?v0 (left$ ?v1 )))):named a47 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_tree$ ))(= (left$ (map_tree$a ?v0 ?v1 ))(map_tree$a ?v0 (left$a ?v1 )))):named a48 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (left$ (map_tree$ ?v0 ?v1 ))(map_tree$ ?v0 (left$ ?v1 )))):named a49 ))
(check-sat )
;(get-unsat-core )
