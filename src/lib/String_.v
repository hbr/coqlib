Require Extraction.
Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.

Set Implicit Arguments.

Extract Inductive ascii =>
"char"
  [ "fun b0 b1 b2 b3 b4 b5 b6 b7 ->
         let f b n -> if b then n else 0 in
         char_of_int (f b0 1 + f b1 2 + f b2 4 + f b3 8
                      + f b4 16 + f b5 32 + f b6 64 + f b7 128)" ].
Extract Inductive string =>
"(int,string)"
  [ "(0,"""")"
         "(fun (c,(p,s))->0,String.make 1 c^String.sub s p (String.length s-p))"
  ]
  "(fun f0 f1 (p,s)->if (String.length s-p)=0 then f0 () else f1 s.[p] (p+1,s))".
