;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_tree_list_a_tree_list_fun$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ (select$ Nat$ )(selecta$ A$ ))(innerNode$ (selectb$ Nat$ )(selectc$ A_tree$ )(selectd$ A_tree$ )))(A_tree_list$ (nil$ )(cons$ (hd$ A_tree$ )(tl$ A_tree_list$ )))(A_tree_list_list$ (nil$a )(cons$a (hd$a A_tree_list$ )(tl$a A_tree_list_list$ )))(A_tree_list_list_list$ (nil$b )(cons$b (hd$b A_tree_list_list$ )(tl$b A_tree_list_list_list$ )))(A_tree_list_list_list_list$ (nil$c )(cons$c (hd$c A_tree_list_list_list$ )(tl$c A_tree_list_list_list_list$ )))))
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun uu$ (A_tree$ )A_tree_list_a_tree_list_fun$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun freq_F$ (A_tree_list$ A$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_tree_list_a_tree_list_fun$ A_tree_list$ )A_tree_list$ )
(declare-fun huffman$ (A_tree_list$ )A_tree$ )
(declare-fun splitLeaf$ (A_tree$ Nat$ A$ Nat$ A$ )A_tree$ )
(declare-fun alphabet_F$ (A_tree_list$ )A_set$ )
(declare-fun splitLeaf_F$ (A_tree_list$ Nat$ A$ Nat$ A$ )A_tree_list$ )
(declare-fun consistent_F$ (A_tree_list$ )Bool )
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(! (= (fun_app$ (uu$ ?v0 )?v1 )(cons$ ?v0 ?v1 )):pattern ((fun_app$ (uu$ ?v0 )?v1 )))):named a0 ))
(assert (! (not (= (splitLeaf$ (huffman$ (cons$ t$ nil$ ))w_a$ a$ w_b$ b$ )(huffman$ (splitLeaf_F$ (cons$ t$ nil$ )w_a$ a$ w_b$ b$ )))):named a1 ))
(assert (! (not (= (cons$ t$ nil$ )nil$ )):named a2 ))
(assert (! (consistent_F$ (cons$ t$ nil$ )):named a3 ))
(assert (! (member$ a$ (alphabet_F$ (cons$ t$ nil$ ))):named a4 ))
(assert (! (= (freq_F$ (cons$ t$ nil$ )a$ )(plus$ w_a$ w_b$ )):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree_list$ )(?v2 Nat$ )(?v3 Nat$ )(?v4 A$ ))(! (=> (not (member$ ?v0 (alphabet_F$ ?v1 )))(= (splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )?v1 )):pattern ((splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )))):named a6 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ )(?v2 Nat$ )(?v3 A$ )(?v4 Nat$ )(?v5 A$ ))(! (= (splitLeaf_F$ (cons$ ?v0 ?v1 )?v2 ?v3 ?v4 ?v5 )(cons$ (splitLeaf$ ?v0 ?v2 ?v3 ?v4 ?v5 )(splitLeaf_F$ ?v1 ?v2 ?v3 ?v4 ?v5 ))):pattern ((splitLeaf_F$ (cons$ ?v0 ?v1 )?v2 ?v3 ?v4 ?v5 )))):named a7 ))
(assert (! (forall ((?v0 A_tree$ ))(! (= (huffman$ (cons$ ?v0 nil$ ))?v0 ):pattern ((uu$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ ))(! (= (splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )nil$ ):pattern ((splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )))):named a9 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (=> (= ?v0 nil$ )false )(and (forall ((?v1 A_tree$ ))(=> (= ?v0 (cons$ ?v1 nil$ ))false ))(forall ((?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3 )))false ))))false )):named a10 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (forall ((?v1 A_tree$ ))(=> (= ?v0 (cons$ ?v1 nil$ ))false ))(and (forall ((?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3 )))false ))(=> (= ?v0 nil$ )false )))false )):named a11 ))
(assert (! (= (consistent_F$ nil$ )true ):named a12 ))
(assert (! (forall ((?v0 A_tree_list_list$ )(?v1 A_tree_list_list_list$ )(?v2 A_tree_list_list$ )(?v3 A_tree_list_list_list$ ))(= (= (cons$b ?v0 ?v1 )(cons$b ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 A_tree_list$ )(?v1 A_tree_list_list$ )(?v2 A_tree_list$ )(?v3 A_tree_list_list$ ))(= (= (cons$a ?v0 ?v1 )(cons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 A_tree_list_list_list$ ))(= (not (= ?v0 nil$b ))(exists ((?v1 A_tree_list_list$ )(?v2 A_tree_list_list_list$ ))(= ?v0 (cons$b ?v1 ?v2 ))))):named a16 ))
(assert (! (forall ((?v0 A_tree_list_list$ ))(= (not (= ?v0 nil$a ))(exists ((?v1 A_tree_list$ )(?v2 A_tree_list_list$ ))(= ?v0 (cons$a ?v1 ?v2 ))))):named a17 ))
(assert (! (forall ((?v0 A_tree_list$ ))(= (not (= ?v0 nil$ ))(exists ((?v1 A_tree$ )(?v2 A_tree_list$ ))(= ?v0 (cons$ ?v1 ?v2 ))))):named a18 ))
(assert (! (forall ((?v0 A_tree_list_list_list$ ))(=> (and (=> (= ?v0 nil$b )false )(and (forall ((?v1 A_tree_list_list$ ))(=> (= ?v0 (cons$b ?v1 nil$b ))false ))(forall ((?v1 A_tree_list_list$ )(?v2 A_tree_list_list$ )(?v3 A_tree_list_list_list$ ))(=> (= ?v0 (cons$b ?v1 (cons$b ?v2 ?v3 )))false ))))false )):named a19 ))
(assert (! (forall ((?v0 A_tree_list_list$ ))(=> (and (=> (= ?v0 nil$a )false )(and (forall ((?v1 A_tree_list$ ))(=> (= ?v0 (cons$a ?v1 nil$a ))false ))(forall ((?v1 A_tree_list$ )(?v2 A_tree_list$ )(?v3 A_tree_list_list$ ))(=> (= ?v0 (cons$a ?v1 (cons$a ?v2 ?v3 )))false ))))false )):named a20 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (=> (= ?v0 nil$ )false )(and (forall ((?v1 A_tree$ ))(=> (= ?v0 (cons$ ?v1 nil$ ))false ))(forall ((?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3 )))false ))))false )):named a21 ))
(assert (! (forall ((?v0 A_tree_list_list_list_list$ ))(=> (and (=> (= ?v0 nil$c )false )(and (forall ((?v1 A_tree_list_list_list_list$ ))(=> (= ?v0 (cons$c nil$b ?v1 ))false ))(forall ((?v1 A_tree_list_list$ )(?v2 A_tree_list_list_list$ )(?v3 A_tree_list_list_list_list$ ))(=> (= ?v0 (cons$c (cons$b ?v1 ?v2 )?v3 ))false ))))false )):named a22 ))
(assert (! (forall ((?v0 A_tree_list_list_list$ ))(=> (and (=> (= ?v0 nil$b )false )(and (forall ((?v1 A_tree_list_list_list$ ))(=> (= ?v0 (cons$b nil$a ?v1 ))false ))(forall ((?v1 A_tree_list$ )(?v2 A_tree_list_list$ )(?v3 A_tree_list_list_list$ ))(=> (= ?v0 (cons$b (cons$a ?v1 ?v2 )?v3 ))false ))))false )):named a23 ))
(assert (! (forall ((?v0 A_tree_list_list$ ))(=> (and (=> (= ?v0 nil$a )false )(and (forall ((?v1 A_tree_list_list$ ))(=> (= ?v0 (cons$a nil$ ?v1 ))false ))(forall ((?v1 A_tree$ )(?v2 A_tree_list$ )(?v3 A_tree_list_list$ ))(=> (= ?v0 (cons$a (cons$ ?v1 ?v2 )?v3 ))false ))))false )):named a24 ))
(assert (! (forall ((?v0 A_tree_list_list_list$ ))(=> (and (=> (= ?v0 nil$b )false )(forall ((?v1 A_tree_list_list$ )(?v2 A_tree_list_list_list$ ))(=> (= ?v0 (cons$b ?v1 ?v2 ))false )))false )):named a25 ))
(assert (! (forall ((?v0 A_tree_list_list$ ))(=> (and (=> (= ?v0 nil$a )false )(forall ((?v1 A_tree_list$ )(?v2 A_tree_list_list$ ))(=> (= ?v0 (cons$a ?v1 ?v2 ))false )))false )):named a26 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (=> (= ?v0 nil$ )false )(forall ((?v1 A_tree$ )(?v2 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 ?v2 ))false )))false )):named a27 ))
(assert (! (forall ((?v0 A_tree_list_list_list$ )(?v1 A_tree_list_list$ )(?v2 A_tree_list_list_list$ ))(=> (= ?v0 (cons$b ?v1 ?v2 ))(not (= ?v0 nil$b )))):named a28 ))
(assert (! (forall ((?v0 A_tree_list_list$ )(?v1 A_tree_list$ )(?v2 A_tree_list_list$ ))(=> (= ?v0 (cons$a ?v1 ?v2 ))(not (= ?v0 nil$a )))):named a29 ))
(assert (! (forall ((?v0 A_tree_list$ )(?v1 A_tree$ )(?v2 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 ?v2 ))(not (= ?v0 nil$ )))):named a30 ))
(check-sat )
;(get-unsat-core )
