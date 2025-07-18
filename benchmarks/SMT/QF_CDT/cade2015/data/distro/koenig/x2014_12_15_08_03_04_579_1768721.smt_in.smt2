;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Num_num_fun$ 0 )
(declare-sort Num_bool_fun$ 0 )
(declare-sort Nat_stream$ 0)
(declare-fun shd$ (Nat_stream$)Nat$)
(declare-fun stl$ (Nat_stream$)Nat_stream$)
(declare-fun sCons$ (Nat$ Nat_stream$ )Nat_stream$)
(declare-datatypes ()((Num$ (one$ )(bit0$ (select$ Num$ ))(bit1$ (selecta$ Num$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun ns$ (Nat$ )Nat_stream$ )
(declare-fun inc$ (Num$ )Num$ )
(declare-fun bitM$ (Num$ )Num$ )
(declare-fun one$a ()Nat$ )
(declare-fun ones$ ()Nat_stream$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun twos$ ()Nat_stream$ )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun plus$a (Num$ )Num_num_fun$ )
(declare-fun plus$b (Nat_stream$ Nat_stream$ )Nat_stream$ )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun scalar$ (Nat$ Nat_stream$ )Nat_stream$ )
(declare-fun times$a (Num$ )Num_num_fun$ )
(declare-fun fun_app$ (Num_num_fun$ Num$ )Num$ )
(declare-fun numeral$ (Num$ )Nat$ )
(declare-fun smember$ (Nat$ Nat_stream$ )Bool )
(declare-fun fun_app$a (Num_bool_fun$ Num$ )Bool )
(assert (! (not (= (scalar$ n$ twos$ )(ns$ (times$ (numeral$ (bit0$ one$ ))n$ )))):named a0 ))
(assert (! (forall ((?v0 Num$ ))(= (= (bit0$ ?v0 )one$ )false )):named a1 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit0$ ?v0 ))false )):named a2 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ )(?v2 Nat$ ))(= (times$ (numeral$ ?v0 )(times$ (numeral$ ?v1 )?v2 ))(times$ (numeral$ (fun_app$ (times$a ?v0 )?v1 ))?v2 ))):named a3 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (times$ (numeral$ ?v0 )(numeral$ ?v1 ))(numeral$ (fun_app$ (times$a ?v0 )?v1 )))):named a4 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (ns$ ?v0 )(scalar$ ?v0 ones$ )):pattern ((ns$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ (numeral$ one$ )?v0 )?v0 )):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 (numeral$ one$ ))?v0 )):named a7 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (numeral$ ?v0 )(numeral$ ?v1 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 Num$ ))(not (= one$ (bit0$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (times$a (bit0$ ?v0 ))(bit0$ ?v1 ))(bit0$ (bit0$ (fun_app$ (times$a ?v0 )?v1 )))):pattern ((fun_app$ (times$a (bit0$ ?v0 ))(bit0$ ?v1 ))))):named a12 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (times$a one$ )?v0 )?v0 ):pattern ((fun_app$ (times$a one$ )?v0 )))):named a13 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (times$a ?v0 )one$ )?v0 ):pattern ((times$a ?v0 )))):named a14 ))
(assert (! (= (= one$ one$ )true ):named a15 ))
(assert (! (= twos$ (sCons$ (numeral$ (bit0$ one$ ))twos$ )):named a16 ))
(assert (! (= (shd$ twos$ )(numeral$ (bit0$ one$ ))):named a17 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 (numeral$ (bit0$ one$ )))(plus$ ?v0 ?v0 ))):named a18 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ (numeral$ (bit0$ one$ ))?v0 )(plus$ ?v0 ?v0 ))):named a19 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (plus$a (bit0$ ?v0 ))(bit0$ ?v1 ))(bit0$ (fun_app$ (plus$a ?v0 )?v1 ))):pattern ((fun_app$ (plus$a (bit0$ ?v0 ))(bit0$ ?v1 ))))):named a20 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (plus$ (numeral$ ?v0 )(numeral$ ?v1 ))(numeral$ (fun_app$ (plus$a ?v0 )?v1 )))):named a21 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ )(?v2 Nat$ ))(= (plus$ (numeral$ ?v0 )(plus$ (numeral$ ?v1 )?v2 ))(plus$ (numeral$ (fun_app$ (plus$a ?v0 )?v1 ))?v2 ))):named a22 ))
(assert (! (= (fun_app$ (plus$a one$ )one$ )(bit0$ one$ )):named a23 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a one$ )?v0 )(fun_app$ (plus$a ?v0 )one$ )):pattern ((fun_app$ (plus$a one$ )?v0 )))):named a24 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(plus$ (times$ ?v2 ?v1 )?v3 ))(plus$ (times$ (plus$ ?v0 ?v2 )?v1 )?v3 ))):named a25 ))
(assert (! (forall ((?v0 Num$ ))(! (= (numeral$ (bit0$ ?v0 ))(plus$ (numeral$ ?v0 )(numeral$ ?v0 ))):pattern ((bit0$ ?v0 )))):named a26 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Num$ ))(= (times$ (plus$ ?v0 ?v1 )(numeral$ ?v2 ))(plus$ (times$ ?v0 (numeral$ ?v2 ))(times$ ?v1 (numeral$ ?v2 ))))):named a27 ))
(assert (! (forall ((?v0 Num$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (numeral$ ?v0 )(plus$ ?v1 ?v2 ))(plus$ (times$ (numeral$ ?v0 )?v1 )(times$ (numeral$ ?v0 )?v2 )))):named a28 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_stream$ )(?v2 Nat$ )(?v3 Nat_stream$ ))(= (= (sCons$ ?v0 ?v1 )(sCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a29 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a30 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a31 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (plus$ ?v0 ?v1 )?v2 )(plus$ ?v0 (plus$ ?v1 ?v2 )))):named a32 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (plus$ ?v0 ?v1 )?v2 )(plus$ ?v0 (plus$ ?v1 ?v2 )))):named a33 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ ?v0 (plus$ ?v1 ?v2 ))(plus$ ?v1 (plus$ ?v0 ?v2 )))):named a34 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (plus$ ?v0 ?v1 )(plus$ ?v1 ?v0 ))):named a35 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a36 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a37 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a38 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(=> (and (= ?v0 ?v1 )(= ?v2 ?v3 ))(= (plus$ ?v0 ?v2 )(plus$ ?v1 ?v3 )))):named a39 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (times$ ?v0 ?v1 )(times$ ?v1 ?v0 ))):named a40 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (times$ ?v1 ?v2 ))(times$ ?v1 (times$ ?v0 ?v2 )))):named a41 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (times$ ?v0 ?v1 )?v2 )(times$ ?v0 (times$ ?v1 ?v2 )))):named a42 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (times$ ?v0 ?v1 )?v2 )(times$ ?v0 (times$ ?v1 ?v2 )))):named a43 ))
(assert (! (forall ((?v0 Nat_stream$ ))(=> (forall ((?v1 Nat$ )(?v2 Nat_stream$ ))(=> (= ?v0 (sCons$ ?v1 ?v2 ))false ))false )):named a44 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (plus$ ?v1 ?v2 ))(plus$ (times$ ?v0 ?v1 )(times$ ?v0 ?v2 )))):named a45 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a46 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(plus$ (times$ ?v2 ?v1 )?v3 ))(plus$ (times$ (plus$ ?v0 ?v2 )?v1 )?v3 ))):named a48 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_stream$ ))(! (= (shd$ (sCons$ ?v0 ?v1 ))?v0 ):pattern ((sCons$ ?v0 ?v1 )))):named a49 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat_stream$ ))(! (= (smember$ ?v0 (sCons$ ?v1 ?v2 ))(ite (= ?v0 ?v1 )true (smember$ ?v0 ?v2 ))):pattern ((smember$ ?v0 (sCons$ ?v1 ?v2 ))))):named a50 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (plus$ ?v1 ?v2 ))(plus$ (times$ ?v0 ?v1 )(times$ ?v0 ?v2 )))):named a51 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a52 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (times$ ?v0 ?v1 )one$a )(and (= ?v0 one$a )(= ?v1 one$a )))):named a53 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= one$a (times$ ?v0 ?v1 ))(and (= ?v0 one$a )(= ?v1 one$a )))):named a54 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 one$a )?v0 )):named a55 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 one$a )?v0 )):named a56 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ one$a ?v0 )?v0 )):named a57 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ one$a ?v0 )?v0 )):named a58 ))
(assert (! (forall ((?v0 Num$ ))(= (= (numeral$ ?v0 )one$a )(= ?v0 one$ ))):named a59 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$a (numeral$ ?v0 ))(= one$ ?v0 ))):named a60 ))
(assert (! (= (plus$ one$a one$a )(numeral$ (bit0$ one$ ))):named a61 ))
(assert (! (forall ((?v0 Num$ ))(= (plus$ (numeral$ ?v0 )one$a )(numeral$ (fun_app$ (plus$a ?v0 )one$ )))):named a62 ))
(assert (! (forall ((?v0 Num$ ))(= (plus$ one$a (numeral$ ?v0 ))(numeral$ (fun_app$ (plus$a one$ )?v0 )))):named a63 ))
(assert (! (forall ((?v0 Nat$ ))(= (= one$a ?v0 )(= ?v0 one$a ))):named a64 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ one$a ?v0 )?v0 )):named a65 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 one$a )?v0 )):named a66 ))
(assert (! (forall ((?v0 Num$ ))(= (plus$ one$a (numeral$ ?v0 ))(plus$ (numeral$ ?v0 )one$a ))):named a67 ))
(assert (! (= (numeral$ one$ )one$a ):named a68 ))
(assert (! (= (numeral$ one$ )one$a ):named a69 ))
(assert (! (= (shd$ ones$ )one$a ):named a70 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a71 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (= (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a72 ))
(assert (! (= ones$ (sCons$ one$a ones$ )):named a73 ))
(assert (! (= (plus$ one$a one$a )(numeral$ (bit0$ one$ ))):named a74 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (plus$ ?v0 (times$ ?v1 ?v0 ))(times$ (plus$ ?v1 one$a )?v0 ))):named a75 ))
(assert (! (forall ((?v0 Nat$ ))(= (plus$ ?v0 ?v0 )(times$ (plus$ one$a one$a )?v0 ))):named a76 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )?v1 )(times$ (plus$ ?v0 one$a )?v1 ))):named a77 ))
(assert (! (forall ((?v0 Num_bool_fun$ )(?v1 Num$ ))(=> (and (fun_app$a ?v0 one$ )(forall ((?v2 Num$ ))(=> (fun_app$a ?v0 ?v2 )(fun_app$a ?v0 (inc$ ?v2 )))))(fun_app$a ?v0 ?v1 ))):named a78 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (fun_app$ (plus$a ?v0 )(inc$ ?v1 ))(inc$ (fun_app$ (plus$a ?v0 )?v1 )))):named a79 ))
(assert (! (= (inc$ one$ )(bit0$ one$ )):named a80 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (plus$ (plus$ ?v0 ?v1 )(plus$ ?v2 ?v3 ))(plus$ (plus$ ?v0 ?v2 )(plus$ ?v1 ?v3 )))):named a81 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (plus$ ?v0 ?v1 )?v2 )(plus$ (plus$ ?v0 ?v2 )?v1 ))):named a82 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (plus$ ?v0 ?v1 )?v2 )(plus$ ?v0 (plus$ ?v1 ?v2 )))):named a83 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ ?v0 (plus$ ?v1 ?v2 ))(plus$ (plus$ ?v0 ?v1 )?v2 ))):named a84 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ ?v0 (plus$ ?v1 ?v2 ))(plus$ ?v1 (plus$ ?v0 ?v2 )))):named a85 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (plus$ ?v0 ?v1 )(plus$ ?v1 ?v0 ))):named a86 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (times$ ?v0 ?v1 )(times$ ?v1 ?v0 ))):named a87 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (times$ ?v1 ?v2 ))(times$ ?v1 (times$ ?v0 ?v2 )))):named a88 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (times$ ?v1 ?v2 ))(times$ (times$ ?v0 ?v1 )?v2 ))):named a89 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (times$ ?v0 ?v1 )?v2 )(times$ ?v0 (times$ ?v1 ?v2 )))):named a90 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (times$ (times$ ?v0 ?v1 )(times$ ?v2 ?v3 ))(times$ ?v0 (times$ ?v1 (times$ ?v2 ?v3 ))))):named a91 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (times$ (times$ ?v0 ?v1 )(times$ ?v2 ?v3 ))(times$ ?v2 (times$ (times$ ?v0 ?v1 )?v3 )))):named a92 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (times$ ?v0 ?v1 )?v2 )(times$ (times$ ?v0 ?v2 )?v1 ))):named a93 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (times$ (times$ ?v0 ?v1 )(times$ ?v2 ?v3 ))(times$ (times$ ?v0 ?v2 )(times$ ?v1 ?v3 )))):named a94 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a ?v0 )one$ )(inc$ ?v0 )):pattern ((plus$a ?v0 )))):named a95 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (fun_app$ (times$a ?v0 )(inc$ ?v1 ))(fun_app$ (plus$a (fun_app$ (times$a ?v0 )?v1 ))?v0 ))):named a96 ))
(assert (! (forall ((?v0 Num$ ))(= (numeral$ (inc$ ?v0 ))(plus$ (numeral$ ?v0 )one$a ))):named a97 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (and (not (= ?v0 ?v1 ))(not (= ?v2 ?v3 )))(not (= (plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v3 ))(plus$ (times$ ?v0 ?v3 )(times$ ?v1 ?v2 )))))):named a98 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ ?v0 (plus$ ?v1 ?v2 ))(plus$ (times$ ?v0 ?v1 )(times$ ?v0 ?v2 )))):named a99 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (times$ (plus$ ?v0 ?v1 )?v2 )(plus$ (times$ ?v0 ?v2 )(times$ ?v1 ?v2 )))):named a100 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (plus$ (times$ ?v0 ?v1 )(times$ ?v2 ?v1 ))(times$ (plus$ ?v0 ?v2 )?v1 ))):named a101 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ )(?v3 Nat$ ))(= (= (plus$ (times$ ?v0 ?v1 )(times$ ?v2 ?v3 ))(plus$ (times$ ?v0 ?v3 )(times$ ?v2 ?v1 )))(or (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a102 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 one$a )?v0 )):named a103 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ one$a ?v0 )?v0 )):named a104 ))
(assert (! (= (bitM$ one$ )one$ ):named a105 ))
(assert (! (forall ((?v0 Num$ ))(= (fun_app$ (plus$a one$ )(bitM$ ?v0 ))(bit0$ ?v0 ))):named a106 ))
(assert (! (forall ((?v0 Num$ ))(= (fun_app$ (plus$a (bitM$ ?v0 ))one$ )(bit0$ ?v0 ))):named a107 ))
(assert (! (forall ((?v0 Nat_stream$ )(?v1 Nat_stream$ ))(= (shd$ (plus$b ?v0 ?v1 ))(plus$ (shd$ ?v0 )(shd$ ?v1 )))):named a108 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit1$ ?v0 )(bit1$ ?v1 ))(= ?v0 ?v1 ))):named a109 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit1$ ?v0 )(bit1$ ?v1 ))(= ?v0 ?v1 ))):named a110 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit1$ ?v0 )(bit0$ ?v1 ))false )):named a111 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit1$ ?v1 ))false )):named a112 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit1$ ?v0 ))false )):named a113 ))
(assert (! (forall ((?v0 Num$ ))(= (= (bit1$ ?v0 )one$ )false )):named a114 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (plus$a (bit1$ ?v0 ))(bit0$ ?v1 ))(bit1$ (fun_app$ (plus$a ?v0 )?v1 ))):pattern ((fun_app$ (plus$a (bit1$ ?v0 ))(bit0$ ?v1 ))))):named a115 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (plus$a (bit0$ ?v0 ))(bit1$ ?v1 ))(bit1$ (fun_app$ (plus$a ?v0 )?v1 ))):pattern ((fun_app$ (plus$a (bit0$ ?v0 ))(bit1$ ?v1 ))))):named a116 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (times$a (bit0$ ?v0 ))(bit1$ ?v1 ))(bit0$ (fun_app$ (times$a ?v0 )(bit1$ ?v1 )))):pattern ((fun_app$ (times$a (bit0$ ?v0 ))(bit1$ ?v1 ))))):named a117 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (times$a (bit1$ ?v0 ))(bit0$ ?v1 ))(bit0$ (fun_app$ (times$a (bit1$ ?v0 ))?v1 ))):pattern ((fun_app$ (times$a (bit1$ ?v0 ))(bit0$ ?v1 ))))):named a118 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (plus$a (bit1$ ?v0 ))(bit1$ ?v1 ))(bit0$ (fun_app$ (plus$a (fun_app$ (plus$a ?v0 )?v1 ))one$ ))):pattern ((fun_app$ (plus$a (bit1$ ?v0 ))(bit1$ ?v1 ))))):named a119 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a (bit1$ ?v0 ))one$ )(bit0$ (fun_app$ (plus$a ?v0 )one$ ))):pattern ((bit1$ ?v0 )))):named a120 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a one$ )(bit1$ ?v0 ))(bit0$ (fun_app$ (plus$a ?v0 )one$ ))):pattern ((bit1$ ?v0 )))):named a121 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a (bit0$ ?v0 ))one$ )(bit1$ ?v0 )):pattern ((bit0$ ?v0 )))):named a122 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (plus$a one$ )(bit0$ ?v0 ))(bit1$ ?v0 )):pattern ((bit0$ ?v0 )))):named a123 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (times$a (bit1$ ?v0 ))(bit1$ ?v1 ))(bit1$ (fun_app$ (plus$a (fun_app$ (plus$a ?v0 )?v1 ))(bit0$ (fun_app$ (times$a ?v0 )?v1 ))))):pattern ((fun_app$ (times$a (bit1$ ?v0 ))(bit1$ ?v1 ))))):named a124 ))
(assert (! (forall ((?v0 Num$ ))(=> (and (=> (= ?v0 one$ )false )(and (forall ((?v1 Num$ ))(=> (= ?v0 (bit0$ ?v1 ))false ))(forall ((?v1 Num$ ))(=> (= ?v0 (bit1$ ?v1 ))false ))))false )):named a125 ))
(assert (! (forall ((?v0 Num$ ))(not (= one$ (bit1$ ?v0 )))):named a126 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(not (= (bit0$ ?v0 )(bit1$ ?v1 )))):named a127 ))
(assert (! (forall ((?v0 Num$ ))(= (bitM$ (bit1$ ?v0 ))(bit1$ (bit0$ ?v0 )))):named a128 ))
(assert (! (forall ((?v0 Num$ ))(! (= (bitM$ (bit0$ ?v0 ))(bit1$ (bitM$ ?v0 ))):pattern ((bit0$ ?v0 )))):named a129 ))
(assert (! (forall ((?v0 Num$ ))(! (= (inc$ (bit0$ ?v0 ))(bit1$ ?v0 )):pattern ((bit0$ ?v0 )))):named a130 ))
(assert (! (forall ((?v0 Num$ ))(! (= (inc$ (bit1$ ?v0 ))(bit0$ (inc$ ?v0 ))):pattern ((bit1$ ?v0 )))):named a131 ))
(assert (! (forall ((?v0 Num$ ))(! (= (numeral$ (bit1$ ?v0 ))(plus$ (plus$ (numeral$ ?v0 )(numeral$ ?v0 ))one$a )):pattern ((bit1$ ?v0 )))):named a132 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ ?v0 (plus$ ?v1 ?v2 )))):named a133 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (minus$ (plus$ ?v0 ?v1 )?v0 )?v1 )):named a134 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (minus$ (plus$ ?v0 ?v1 )?v1 )?v0 )):named a135 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (plus$ ?v0 ?v1 )(plus$ ?v0 ?v2 ))(minus$ ?v1 ?v2 ))):named a136 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (plus$ ?v0 ?v1 )(plus$ ?v2 ?v1 ))(minus$ ?v0 ?v2 ))):named a137 ))
(check-sat )
;(get-unsat-core )
